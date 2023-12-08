// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice.customize;

import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import software.amazon.polymorph.smithypython.common.customize.CustomFileWriter;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.common.shapevisitor.ShapeVisitorResolver;
import software.amazon.polymorph.smithypython.localservice.extensions.DafnyPythonLocalServiceStructureGenerator;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.codegen.core.TopologicalIndex;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.StructureGenerator;
import software.amazon.smithy.python.codegen.SymbolVisitor;
import software.amazon.smithy.python.codegen.UnionGenerator;
import software.amazon.smithy.utils.CaseUtils;


/**
 * Extends the Smithy-Python-generated models.py file
 * by adding Dafny plugin models.
 */
public class ReferencesFileWriter implements CustomFileWriter {
  @Override
  public void customizeFileForServiceShape(
      ServiceShape serviceShape, GenerationContext codegenContext) {
    String moduleName = SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(codegenContext.settings().getService().getNamespace());
    System.out.println("customize references for serviceshape " + serviceShape.getId());
    codegenContext.writerDelegator().useFileWriter(moduleName + "/references.py", "", writer -> {

      writer.write(
          """
             ${C|}
              """,
          writer.consumer(w -> generateServiceOperationModelShapes(codegenContext, serviceShape, w))
      );
    });
  }

  /**
   * Generate service operation input and output shapes.
   * Operations on the service are defined in client.py.
   * This client will expect to take in the input shape types defined here,
   *   and will return the output shape types defined here.
   * @param codegenContext
   * @param serviceShape
   * @param writer
   */
  private void generateServiceOperationModelShapes(
      GenerationContext codegenContext, ServiceShape serviceShape, PythonWriter writer) {

    // Parse operation input and output shapes to retrieve any reference shapes,
    //   which are shapes tagged with the `@aws.polymorph#reference` trait.
    Set<ShapeId> inputAndOutputShapeIds = new HashSet<>();
    for (ShapeId operationShapeId : serviceShape.getOperations()) {
      OperationShape operationShape = codegenContext.model()
          .expectShape(operationShapeId, OperationShape.class);
      inputAndOutputShapeIds.add(operationShape.getInputShape());
      inputAndOutputShapeIds.add(operationShape.getOutputShape());
    }
    Set<MemberShape> referenceMemberShapes = new HashSet<>();
    referenceMemberShapes.addAll(
        ModelUtils.findAllDependentMemberReferenceShapes(inputAndOutputShapeIds, codegenContext.model())
    );

    // Parse reference shapes to retrieve the underlying Resource or Service shape
    Set<Shape> referenceChildShape = new HashSet<>();
    for (MemberShape referenceMemberShape : referenceMemberShapes) {
      Shape referenceShape = codegenContext.model().expectShape(referenceMemberShape.getTarget());
      ReferenceTrait referenceTrait = referenceShape.expectTrait(ReferenceTrait.class);
      Shape resourceOrService = codegenContext.model().expectShape(referenceTrait.getReferentId());
      referenceChildShape.add(resourceOrService);
    }

    // For each reference shape, generate an interface and an implementation shape
    for(Shape resourceOrServiceShape : referenceChildShape) {
      generateResourceStuff(resourceOrServiceShape, codegenContext, writer);
    }
  }

  public void generateResourceStuff(Shape resourceOrServiceShape, GenerationContext context, PythonWriter writer) {
    if (!resourceOrServiceShape.getId().getNamespace().equals(context.settings().getService().getNamespace())) {
      return;
    }
    System.out.println("generating resourcestuff for " + resourceOrServiceShape.getId());
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
    writer.write("""
        
        class I$L(metaclass=abc.ABCMeta):
            @classmethod
            def __subclasshook__(cls, subclass):
                return (
                    ${C|}
                )
                
            # TODO-Python: Add impl with typehint to ABC
                
            ${C|}
        """,
        resourceOrServiceShape.getId().getName(),
        writer.consumer(w -> generateInterfaceSubclasshookExpressionForResourceOrService(
            context, resourceOrServiceShape, w)
        ),
        writer.consumer(w -> generateInterfaceOperationFunctionDefinitionForResourceOrService(
            context, resourceOrServiceShape, w)
        )
    );

    writer.addStdlibImport("typing", "Any");

    // Write implementation for reference shape
    writer.write("""
        class $L(I$L):
            # TODO-Python: typehint
            _impl: Any
            
            def __init__(self, _impl):
                self._impl = _impl
                
            ${C|}
        """,
        resourceOrServiceShape.getId().getName(),
        resourceOrServiceShape.getId().getName(),
        writer.consumer(w -> generateSmithyOperationFunctionDefinitionForResourceOrService(
            context, resourceOrServiceShape, w)
        )
    );
  }

  /**
   * Generates the expression that validates that a class that claims to implement an interface
   *   implements all required operations.
   * @param codegenContext
   * @param resourceOrService
   * @param writer
   */
  private void generateInterfaceSubclasshookExpressionForResourceOrService(
      GenerationContext codegenContext, Shape resourceOrService, PythonWriter writer) {
    if (resourceOrService.asServiceShape().isPresent()) {
      generateInterfaceSubclasshookExpressionForService(codegenContext,
          resourceOrService.asServiceShape().get(), writer);
    } else if (resourceOrService.asResourceShape().isPresent()) {
      generateInterfaceSubclasshookExpressionForResource(codegenContext,
          resourceOrService.asResourceShape().get(), writer);
    } else {
      throw new IllegalArgumentException("Shape MUST be a resource or a service: " + resourceOrService);
    }
  }

  /**
   * Generates the expression that validates that a class that claims to implement a service interface
   *   implements all required operations.
   * @param codegenContext
   * @param serviceShape
   * @param writer
   */
  private void generateInterfaceSubclasshookExpressionForService(
      GenerationContext codegenContext, ServiceShape serviceShape, PythonWriter writer) {
    List<ShapeId> operationList = serviceShape.getOperations().stream().toList();
    Iterator<ShapeId> operationListIterator = operationList.iterator();

    generateInterfaceSubclasshookExpressionForOperations(codegenContext, operationListIterator, writer);
  }

  /**
   * Generates the expression that validates that a class that claims to implement a resource interface
   *   implements all required operations.
   * @param codegenContext
   * @param resourceShape
   * @param writer
   */
  private void generateInterfaceSubclasshookExpressionForResource(
      GenerationContext codegenContext, ResourceShape resourceShape, PythonWriter writer) {
    List<ShapeId> operationList = resourceShape.getOperations().stream().toList();
    Iterator<ShapeId> operationListIterator = operationList.iterator();

    generateInterfaceSubclasshookExpressionForOperations(codegenContext, operationListIterator, writer);
  }

  /**
   * Generates the expression that validates that a class that claims to implement the resource
   *   or service with the provided list of operations implements all of the operations.
   * @param codegenContext
   * @param operationListIterator
   * @param writer
   */
  private void generateInterfaceSubclasshookExpressionForOperations(
      GenerationContext codegenContext, Iterator<ShapeId> operationListIterator, PythonWriter writer) {
    // For all but the last operation shape, generate `hasattr and callable and`
    // For the last shape, generate `hasattr and callable`
    while (operationListIterator.hasNext()) {
      ShapeId operationShapeId = operationListIterator.next();
      writer.writeInline("""
          hasattr(subclass, "$L") and callable(subclass.$L)""",
          operationShapeId.getName(), operationShapeId.getName()
      );
      if (operationListIterator.hasNext()) {
        writer.write(" and");
      }
    }
  }

  /**
   * Generates abstract methods for all operations on the provided resourceOrService.
   * This is called from a resourceOrService interface to generate its abstract methods.
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
      throw new IllegalArgumentException("Shape MUST be a resource or a service: " + resourceOrService);
    }

    for (ShapeId operationShapeId : operationShapeIds) {
      writer.write("""
          @abc.abstractmethod
          def $L(self, native_input):
              raise NotImplementedError
          """, operationShapeId.getName());
    }
  }

  /**
   * Generates methods for all operations on the provided resourceOrService.
   * The generated method takes in a native type input and returns a native type output.
   * Internally, the method will convert the native type to a Dafny type,
   *   call the Dafny implementation with the Dafny type,
   *   receive a Dafny type from the Dafny implementation,
   *   convert the Dafny type back to the corresponding native type,
   *   and then return the native type.
   * This is called from a concrete resourceOrService.
   * @param codegenContext
   * @param resourceOrService
   * @param writer
   */
  private void generateSmithyOperationFunctionDefinitionForResourceOrService(
      GenerationContext codegenContext, Shape resourceOrService, PythonWriter writer) {
    Set<ShapeId> operationShapeIds;
    if (resourceOrService.asServiceShape().isPresent()) {
      operationShapeIds = resourceOrService.asServiceShape().get().getOperations();
    } else if (resourceOrService.asResourceShape().isPresent()) {
      operationShapeIds = resourceOrService.asResourceShape().get().getOperations();
    } else {
      throw new IllegalArgumentException("Shape MUST be a resource or a service: " + resourceOrService);
    }

    for (ShapeId operationShapeId : operationShapeIds) {
      OperationShape operationShape = codegenContext.model().expectShape(operationShapeId, OperationShape.class);

      Shape targetShapeInput = codegenContext.model().expectShape(operationShape.getInputShape());
      var inputSymbol = codegenContext.symbolProvider().toSymbol(targetShapeInput);
      // Generate code that converts the input from the Dafny type to the corresponding Smithy type
      // `input` will hold a string that converts the Dafny `input` to the Smithy-modelled output.
      // This has a side effect of possibly writing transformation code at the writer's current position.
      // For example, a service shape may require some calls to `ctor__()` after it is created,
      //   and cannot be constructed inline.
      // Polymorph will create an object representing the service's client, instantiate it,
      //   then reference that object in its `input` string.
      String input = targetShapeInput.accept(ShapeVisitorResolver.getToDafnyShapeVisitorForShape(targetShapeInput,
          codegenContext,
          "native_input",
          writer
      ));

      Shape targetShape = codegenContext.model().expectShape(operationShape.getOutputShape());
      var outputSymbol = codegenContext.symbolProvider().toSymbol(targetShape);
      // Generate output code converting the return value of the Dafny implementation into
      // its corresponding native-modelled type.
      String output = targetShape.accept(ShapeVisitorResolver.getToNativeShapeVisitorForShape(targetShape, 
          codegenContext,
          "dafny_output",
          writer
      ));

      writer.write("""
          def $L(self, native_input):
              dafny_output = self._impl.$L($L)
              return $L
          """, operationShapeId.getName(),
          operationShapeId.getName(),
          input,
          output
      );
    }
  }

  /**
   * Writes code modelling inputs and outputs for the provided operationShapeIds.
   * These operationShapeIds MUST NOT be members of the localService provided in the
   *   `customizeFileForServiceShape` method in this file.
   * @param shapeIds
   * @param codegenContext
   */
  @Override
  public void customizeFileForNonServiceShapes(Set<ShapeId> shapeIds, GenerationContext codegenContext) {
    // Write out a Smithy-modelled structure for all operation shapes.
//    for (ShapeId operationShapeId : shapeIds) {
//
//      if (codegenContext.model().expectShape(operationShapeId).isOperationShape()) {
//        //      System.out.println(operationShapeId);
//        OperationShape operationShape = codegenContext.model().expectShape(operationShapeId, OperationShape.class);
//        StructureShape inputShape = codegenContext.model().expectShape(operationShape.getInputShape(), StructureShape.class);
////      writeStructureShape(inputShape, codegenContext);
//        var inputSymbol = codegenContext.symbolProvider().toSymbol(inputShape);
//        StructureShape outputShape = codegenContext.model().expectShape(operationShape.getOutputShape(), StructureShape.class);
////      writeStructureShape(outputShape, codegenContext);
//        var outputSymbol = codegenContext.symbolProvider().toSymbol(outputShape);
//
//        String moduleName = SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(codegenContext.settings().getService().getNamespace());
//        codegenContext.writerDelegator().useFileWriter(moduleName + "/models.py", "", writer -> {
//
////        inputShape.accept(new SymbolVisitor(codegenContext.model(), codegenContext.settings()));
////        outputShape.accept(new SymbolVisitor(codegenContext.model(), codegenContext.settings()));
////        inputShape.accept(ShapeVisitorResolver.getToNativeShapeVisitorForShape(inputShape, codegenContext, "input", writer));
////        outputShape.accept(ShapeVisitorResolver.getToNativeShapeVisitorForShape(outputShape, codegenContext, "input", writer));
//
////
////        inputShape.accept(ShapeVisitorResolver.getToDafnyShapeVisitorForShape(inputShape, codegenContext, "input", writer));
////        outputShape.accept(ShapeVisitorResolver.getToDafnyShapeVisitorForShape(outputShape, codegenContext, "input", writer));
////        inputShape.accept(ShapeVisitorResolver.getToNativeShapeVisitorForShape(inputShape, codegenContext, "input", writer));
////        outputShape.accept(ShapeVisitorResolver.getToNativeShapeVisitorForShape(outputShape, codegenContext, "input", writer));
//
//        });
//      }
//
//      else {
//
//      }
//
//    }
  }

  /**
   * Writes code modelling the provided StructureShape.
   * This relies on a fork of Smithy-Python which makes its StructureGenerator public.
   * Smithy-Python does not generate code to model shapes that are not used
   *   by the service under generation.
   * Polymorph takes Smithy-Python's StructureGenerator and executes it for these shapes,
   *   as it must generate code modelling shapes that are not directly used by the service
   *   under generation. (Services that rely on this service may still use these operations/shapes.)
   * @param structureShape
   * @param codegenContext
   */
  private void writeStructureShape(StructureShape structureShape, GenerationContext codegenContext) {
    if (structureShape.getId().getNamespace().equals(codegenContext.settings().getService().getNamespace())) {
      codegenContext.writerDelegator().useShapeWriter(
          structureShape,
          writer -> {
            DafnyPythonLocalServiceStructureGenerator generator = new DafnyPythonLocalServiceStructureGenerator(
                codegenContext.model(),
                codegenContext.settings(),
                codegenContext.symbolProvider(),
                writer,
                structureShape,
                TopologicalIndex.of(codegenContext.model()).getRecursiveShapes()
            );
            generator.run();
          }
      );

      // TODO-Python: Necessary?
      for (MemberShape memberShape : structureShape.getAllMembers().values()) {
        if (codegenContext.model().expectShape(memberShape.getTarget()).isStructureShape()) {
          writeStructureShape(codegenContext.model().expectShape(memberShape.getTarget()).asStructureShape().get(), codegenContext);
        } else if (codegenContext.model().expectShape(memberShape.getTarget()).isUnionShape()) {
          writeUnionShape(codegenContext.model().expectShape(memberShape.getTarget()).asUnionShape().get(), codegenContext);
        }
      }
    }

  }

  private void writeUnionShape(UnionShape unionShape, GenerationContext codegenContext) {
    if (unionShape.getId().getNamespace()
        .equals(codegenContext.settings().getService().getNamespace())) {

      codegenContext.writerDelegator().useShapeWriter(
          unionShape,
          writer -> {
            UnionGenerator generator = new UnionGenerator(
                codegenContext.model(),
                codegenContext.symbolProvider(),
                writer,
                unionShape,
                TopologicalIndex.of(codegenContext.model()).getRecursiveShapes()
            );
            generator.run();
          }
      );

      // TODO-Python: Necessary?
      for (MemberShape memberShape : unionShape.getAllMembers().values()) {
        if (codegenContext.model().expectShape(memberShape.getTarget()).isStructureShape()) {
          writeStructureShape(
              codegenContext.model().expectShape(memberShape.getTarget()).asStructureShape().get(),
              codegenContext);
        } else if (codegenContext.model().expectShape(memberShape.getTarget()).isUnionShape()) {
          writeUnionShape(
              codegenContext.model().expectShape(memberShape.getTarget()).asUnionShape().get(),
              codegenContext);
        }
      }
    }
  }
}
