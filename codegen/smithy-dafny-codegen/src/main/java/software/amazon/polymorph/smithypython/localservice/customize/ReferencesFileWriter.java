// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice.customize;

import java.util.Iterator;
import java.util.List;
import java.util.Set;

import software.amazon.polymorph.smithypython.common.customize.CustomFileWriter;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.shapevisitor.ShapeVisitorResolver;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/** Extends the Smithy-Python-generated models.py file by adding Dafny plugin models. */
public class ReferencesFileWriter implements CustomFileWriter {
  @Override
  public void customizeFileForServiceShape(
      ServiceShape serviceShape, GenerationContext codegenContext) {
    // Legacy stub
  }

  public void generateResourceInterfaceAndImplementation(Shape resourceOrServiceShape, GenerationContext codegenContext, PythonWriter writer) {
    generateResourceInterface(resourceOrServiceShape, codegenContext, writer);
    generateResourceImplementation(resourceOrServiceShape, codegenContext, writer);
  }

  public void generateResourceInterface(
      Shape resourceOrServiceShape, GenerationContext context, PythonWriter writer) {
    // Only generate resources in the service namespace
    if (!resourceOrServiceShape
        .getId()
        .getNamespace()
        .equals(context.settings().getService().getNamespace())) {
      return;
    }
    // Write reference interface.
    // We use the `abc` (Abstract Base Class) library to define a stricter interface contract
    //   for references in Python than a standard Python subclass contract.
    // The generated code will use the ABC library to enforce constraints at object-create time.
    // In particular, when the object is constructed, the constructor will validate that the
    //   object's class implements all callable operations defined in the reference's Smithy model.
    // This differs from standard Python duck-typing, where classes implementing an "interface" are
    //   only checked that an "interface" operation is implemented at operation call-time.
    // We do this for a number of reasons:
    //   1) This is a Smithy-Dafny code generator, and Dafny has this stricter interface
    //      contract. We decide to generate code that biases toward the Dafny behavior;
    //   2) A strict interface contract will detect issues implementing an interface sooner.
    // This is opinionated and may change.
    writer.addStdlibImport("abc");
    writer.write(
        """

            class I$L(metaclass=abc.ABCMeta):
                @classmethod
                def __subclasshook__(cls, subclass):
                    return (
                        ${C|}
                    )

                ${C|}
            """,
        resourceOrServiceShape.getId().getName(),
        writer.consumer(
            w ->
                generateInterfaceSubclasshookExpressionForResourceOrService(
                    context, resourceOrServiceShape, w)),
        writer.consumer(
            w ->
                generateInterfaceOperationFunctionDefinitionForResourceOrService(
                    context, resourceOrServiceShape, w)));

    writer.addStdlibImport("typing", "Any");
  }

  public void generateResourceImplementation(
      Shape resourceOrServiceShape, GenerationContext context, PythonWriter writer) {
    // Only generate resources in the service namespace
    if (!resourceOrServiceShape
        .getId()
        .getNamespace()
        .equals(context.settings().getService().getNamespace())) {
      return;
    }

    String dafnyInterfaceTypeName;
    if (resourceOrServiceShape.isResourceShape()) {
      ResourceShape resourceShape = resourceOrServiceShape.asResourceShape().get();
      dafnyInterfaceTypeName = DafnyNameResolver.getDafnyInterfaceTypeForResourceShape(resourceShape);
    } else {
      ServiceShape serviceShape = resourceOrServiceShape.asServiceShape().get();
      dafnyInterfaceTypeName = DafnyNameResolver.getDafnyClientInterfaceTypeForServiceShape(serviceShape);
    }

    writer.addStdlibImport(DafnyNameResolver.getDafnyPythonTypesModuleNameForShape(resourceOrServiceShape));

    // Write implementation for reference shape
    writer.write(
        """
        class $1L(I$1L):
            _impl: $2L

            def __init__(self, _impl):
                self._impl = _impl

            ${3C|}
            
            ${4C|}
        """,
        resourceOrServiceShape.getId().getName(),
        DafnyNameResolver.getDafnyPythonTypesModuleNameForShape(resourceOrServiceShape) + "." + dafnyInterfaceTypeName,
        writer.consumer(
            w ->
                generateSmithyOperationFunctionDefinitionForResource(
                    context, resourceOrServiceShape, w)),
        writer.consumer(
            w ->
                generateDictConvertersForResource(
                    resourceOrServiceShape, w)));
  }

  /**
   * Generates the expression that validates that a class that claims to implement an interface
   * implements all required operations.
   *
   * @param codegenContext
   * @param resourceOrService
   * @param writer
   */
  private void generateInterfaceSubclasshookExpressionForResourceOrService(
      GenerationContext codegenContext, Shape resourceOrService, PythonWriter writer) {
    if (resourceOrService.asServiceShape().isPresent()) {
      generateInterfaceSubclasshookExpressionForService(
          codegenContext, resourceOrService.asServiceShape().get(), writer);
    } else if (resourceOrService.asResourceShape().isPresent()) {
      generateInterfaceSubclasshookExpressionForResource(
          codegenContext, resourceOrService.asResourceShape().get(), writer);
    } else {
      throw new IllegalArgumentException(
          "Shape MUST be a resource or a service: " + resourceOrService);
    }
  }

  /**
   * Generates the expression that validates that a class that claims to implement a service
   * interface implements all required operations.
   *
   * @param codegenContext
   * @param serviceShape
   * @param writer
   */
  private void generateInterfaceSubclasshookExpressionForService(
      GenerationContext codegenContext, ServiceShape serviceShape, PythonWriter writer) {
    List<ShapeId> operationList = serviceShape.getOperations().stream().toList();
    Iterator<ShapeId> operationListIterator = operationList.iterator();

    generateInterfaceSubclasshookExpressionForOperations(
        codegenContext, operationListIterator, writer);
  }

  /**
   * Generates the expression that validates that a class that claims to implement a resource
   * interface implements all required operations.
   *
   * @param codegenContext
   * @param resourceShape
   * @param writer
   */
  private void generateInterfaceSubclasshookExpressionForResource(
      GenerationContext codegenContext, ResourceShape resourceShape, PythonWriter writer) {
    List<ShapeId> operationList = resourceShape.getOperations().stream().toList();
    Iterator<ShapeId> operationListIterator = operationList.iterator();

    generateInterfaceSubclasshookExpressionForOperations(
        codegenContext, operationListIterator, writer);
  }

  /**
   * Generates the expression that validates that a class that claims to implement the resource or
   * service with the provided list of operations implements all of the operations.
   *
   * @param codegenContext
   * @param operationListIterator
   * @param writer
   */
  private void generateInterfaceSubclasshookExpressionForOperations(
      GenerationContext codegenContext,
      Iterator<ShapeId> operationListIterator,
      PythonWriter writer) {
    // For all but the last operation shape, generate `hasattr and callable and`
    // For the last shape, generate `hasattr and callable`
    while (operationListIterator.hasNext()) {
      ShapeId operationShapeId = operationListIterator.next();
      writer.writeInline(
          """
          hasattr(subclass, "$L") and callable(subclass.$L)""",
          operationShapeId.getName(),
          operationShapeId.getName());
      if (operationListIterator.hasNext()) {
        writer.write(" and");
      }
    }
  }

  /**
   * Generates abstract methods for all operations on the provided resourceOrService. This is called
   * from a resourceOrService interface to generate its abstract methods.
   *
   * @param codegenContext
   * @param resourceOrService
   * @param writer
   */
  private void generateInterfaceOperationFunctionDefinitionForResourceOrService(
      GenerationContext codegenContext, Shape resourceOrService, PythonWriter writer) {
    Set<ShapeId> operationShapeIds;
    if (resourceOrService.asServiceShape().isPresent()) {
      operationShapeIds = resourceOrService.asServiceShape().get().getOperations();
    } else if (resourceOrService.asResourceShape().isPresent()) {
      operationShapeIds = resourceOrService.asResourceShape().get().getOperations();
    } else {
      throw new IllegalArgumentException(
          "Shape MUST be a resource or a service: " + resourceOrService);
    }

    for (ShapeId operationShapeId : operationShapeIds) {
      writer.write(
          """
          @abc.abstractmethod
          def $L(self, native_input):
              raise NotImplementedError
          """,
          operationShapeId.getName());
    }
  }

  /**
   * Generates methods for all operations on the provided resourceOrService. The generated method
   * takes in a native type input and returns a native type output. Internally, the method will
   * convert the native type to a Dafny type, call the Dafny implementation with the Dafny type,
   * receive a Dafny type from the Dafny implementation, convert the Dafny type back to the
   * corresponding native type, and then return the native type. This is called from a concrete
   * resourceOrService.
   *
   * @param codegenContext
   * @param resourceOrService
   * @param writer
   */
  private void generateSmithyOperationFunctionDefinitionForResource(
      GenerationContext codegenContext, Shape resourceOrService, PythonWriter writer) {
    Set<ShapeId> operationShapeIds;
    if (resourceOrService.asServiceShape().isPresent()) {
      operationShapeIds = resourceOrService.asServiceShape().get().getOperations();
    } else if (resourceOrService.asResourceShape().isPresent()) {
      operationShapeIds = resourceOrService.asResourceShape().get().getOperations();
    } else {
      throw new IllegalArgumentException(
          "Shape MUST be a resource or a service: " + resourceOrService);
    }

    for (ShapeId operationShapeId : operationShapeIds) {
      OperationShape operationShape =
          codegenContext.model().expectShape(operationShapeId, OperationShape.class);

      Shape targetShapeInput = codegenContext.model().expectShape(operationShape.getInputShape());
      var inputSymbol = codegenContext.symbolProvider().toSymbol(targetShapeInput);
      // Generate code that converts the input from the Dafny type to the corresponding Smithy type
      // `input` will hold a string that converts the Dafny `input` to the Smithy-modelled output.
      // This has a side effect of possibly writing transformation code at the writer's current
      // position.
      // For example, a service shape may require some calls to `ctor__()` after it is created,
      //   and cannot be constructed inline.
      // Polymorph will create an object representing the service's client, instantiate it,
      //   then reference that object in its `input` string.
      String input =
          targetShapeInput.accept(
              ShapeVisitorResolver.getToDafnyShapeVisitorForShape(
                  targetShapeInput, codegenContext, "native_input", writer));

      Shape targetShape = codegenContext.model().expectShape(operationShape.getOutputShape());
      // Generate output code converting the return value of the Dafny implementation into
      // its corresponding native-modelled type.
      String output =
          targetShape.accept(
              ShapeVisitorResolver.getToNativeShapeVisitorForShape(
                  targetShape, codegenContext, "dafny_output", writer));

      writer.write(
          """
          def $L(self, native_input):
              dafny_output = self._impl.$L($L)
              return $L
          """,
          operationShapeId.getName(),
          operationShapeId.getName(),
          input,
          output);
    }
  }

  /**
   * Writes `as_dict` and `from_dict` methods on the reference shape.
   *   These convert the shape to/from a dictionary and help with compatability across
   *   other shapes' as/from dict conversions.
   * @param codegenContext
   * @param resourceOrService
   * @param writer
   */
  private void generateDictConvertersForResource(
          Shape resourceOrService, PythonWriter writer) {

    writer.addStdlibImport("typing", "Dict");
    writer.addStdlibImport("typing", "Any");

    writer.write("@staticmethod");
    writer.openBlock("def from_dict(d: Dict[str, Any]) -> '$L':",
            "",
            resourceOrService.getId().getName(),
            () -> {
                writer.write("return $L(d['_impl'])", resourceOrService.getId().getName());
            });

    writer.openBlock("def as_dict(self) -> Dict[str, Any]:",
            "",
            () -> {
              writer.write("return {'_impl': self._impl}");
            });

  }
}
