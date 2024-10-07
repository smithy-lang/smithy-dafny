// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice.customize;

import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Set;
import software.amazon.polymorph.smithypython.common.customize.CustomFileWriter;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.common.shapevisitor.ShapeVisitorResolver;
import software.amazon.polymorph.traits.ExtendableTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.model.shapes.*;
import software.amazon.smithy.model.traits.DocumentationTrait;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.utils.CaseUtils;

/**
 * Writes references ({@link ResourceShape}s with a {@link
 * software.amazon.polymorph.traits.ReferenceTrait}) to a `references.py` file. References are
 * separated from the `models.py` file to avoid circular import issues.
 */
public class ReferencesFileWriter implements CustomFileWriter {

  private static final Set<ShapeId> generatedResourceShapes = new HashSet<>();

  public static boolean hasGeneratedResourceForShape(ShapeId shapeId) {
    return generatedResourceShapes.contains(shapeId);
  }

  public static boolean shouldGenerateResourceForShape(
    ResourceShape resourceShape,
    GenerationContext codegenContext
  ) {
    return (
      !hasGeneratedResourceForShape(resourceShape.getId()) &&
      resourceShape
        .getId()
        .getNamespace()
        .equals(codegenContext.settings().getService().getNamespace())
    );
  }

  public void generateResourceInterfaceAndImplementation(
    ResourceShape resourceShape,
    GenerationContext codegenContext,
    PythonWriter writer
  ) {
    if (shouldGenerateResourceForShape(resourceShape, codegenContext)) {
      generatedResourceShapes.add(resourceShape.getId());
      if (resourceShape.hasTrait(ExtendableTrait.class)) {
        generateResourceInterface(resourceShape, codegenContext, writer);
      }
      generateResourceImplementation(resourceShape, codegenContext, writer);
    }
  }

  protected void generateResourceInterface(
    ResourceShape resourceShape,
    GenerationContext context,
    PythonWriter writer
  ) {
    // Only generate resources in the service namespace
    if (
      !resourceShape
        .getId()
        .getNamespace()
        .equals(context.settings().getService().getNamespace())
    ) {
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
          ${C|}
          @classmethod
          def __subclasshook__(cls, subclass):
              return (
                  ${C|}
              )

          ${C|}

          ${C|}


      """,
      resourceShape.getId().getName(),
      writer.consumer(w ->
        writeDocsForResourceOrInterfaceClass(writer, resourceShape, context)
      ),
      writer.consumer(w ->
        generateInterfaceSubclasshookExpressionForResource(
          context,
          resourceShape,
          w
        )
      ),
      writer.consumer(w ->
        generateInterfaceOperationFunctionDefinitionForResource(
          context,
          resourceShape,
          w
        )
      ),
      writer.consumer(w ->
        generateNativeWrapperFunctionDefinitionForResource(
          context,
          resourceShape,
          w
        )
      )
    );

    writer.addStdlibImport("typing", "Any");
  }

  protected void generateResourceImplementation(
    ResourceShape resourceShape,
    GenerationContext context,
    PythonWriter writer
  ) {
    // Only generate resources in the service namespace
    if (
      !resourceShape
        .getId()
        .getNamespace()
        .equals(context.settings().getService().getNamespace())
    ) {
      return;
    }

    String dafnyInterfaceTypeName =
      DafnyNameResolver.getDafnyInterfaceTypeForResourceShape(resourceShape);
    writer.addStdlibImport(
      DafnyNameResolver.getDafnyPythonTypesModuleNameForShape(
        resourceShape,
        context
      )
    );

    // Write implementation for resource shape
    writer.write(
      """
      class $1L$6L:
          ${5C|}
          _impl: $2L

          def __init__(self, _impl: $2L):
              self._impl = _impl

          ${3C|}

          ${4C|}
      """,
      resourceShape.getId().getName(),
      DafnyNameResolver.getDafnyPythonTypesModuleNameForShape(
        resourceShape,
        context
      ) +
      "." +
      dafnyInterfaceTypeName,
      writer.consumer(w ->
        generateSmithyOperationFunctionDefinitionForResource(
          context,
          resourceShape,
          w
        )
      ),
      writer.consumer(w -> generateDictConvertersForResource(resourceShape, w)),
      writer.consumer(w ->
        writeDocsForResourceOrInterfaceClass(w, resourceShape, context)
      ),
      // Only extend interface if extendable;
      // otherwise doesn't extend anything
      resourceShape.hasTrait(ExtendableTrait.class)
        ? "(I%1$s)".formatted(resourceShape.getId().getName())
        : ""
    );
  }

  /**
   * Generates the expression that validates that a class that claims to implement an interface
   * implements all required operations.
   *
   * @param codegenContext
   * @param resourceShape
   * @param writer
   */
  private void generateInterfaceSubclasshookExpressionForResource(
    GenerationContext codegenContext,
    ResourceShape resourceShape,
    PythonWriter writer
  ) {
    List<ShapeId> operationList = resourceShape
      .getOperations()
      .stream()
      .toList();
    Iterator<ShapeId> operationListIterator = operationList.iterator();

    // For all but the last operation shape, generate `hasattr and callable and`
    // For the last shape, generate `hasattr and callable`
    while (operationListIterator.hasNext()) {
      ShapeId operationShapeId = operationListIterator.next();
      writer.writeInline(
        """
        hasattr(subclass, "$L") and callable(subclass.$L)""",
        operationShapeId.getName(),
        operationShapeId.getName()
      );
      if (operationListIterator.hasNext()) {
        writer.write(" and");
      }
    }
  }

  /**
   * Generates abstract methods for all operations on the provided resource. This is called from a
   * resource interface to generate its abstract methods.
   *
   * @param codegenContext
   * @param resourceShape
   * @param writer
   */
  private void generateInterfaceOperationFunctionDefinitionForResource(
    GenerationContext codegenContext,
    ResourceShape resourceShape,
    PythonWriter writer
  ) {
    Set<ShapeId> operationShapeIds = resourceShape.getOperations();

    for (ShapeId operationShapeId : operationShapeIds) {
      writer.write("@abc.abstractmethod");

      OperationShape operationShape = codegenContext
        .model()
        .expectShape(operationShapeId, OperationShape.class);

      Shape targetShapeInput = codegenContext
        .model()
        .expectShape(operationShape.getInputShape());
      SmithyNameResolver.importSmithyGeneratedTypeForShape(
        writer,
        targetShapeInput,
        codegenContext
      );
      Symbol inputSymbol = codegenContext
        .symbolProvider()
        .toSymbol(targetShapeInput);

      Shape targetShapeOutput = codegenContext
        .model()
        .expectShape(operationShape.getOutputShape());
      SmithyNameResolver.importSmithyGeneratedTypeForShape(
        writer,
        targetShapeOutput,
        codegenContext
      );
      Symbol outputSymbol = codegenContext
        .symbolProvider()
        .toSymbol(targetShapeOutput);

      writer.openBlock(
        "def $L(self, param: '$L') -> '$L':",
        "",
        CaseUtils.toSnakeCase(operationShapeId.getName()),
        inputSymbol,
        outputSymbol,
        () -> {
          writeDocsForResourceOrInterfaceOperation(
            writer,
            codegenContext
              .model()
              .expectShape(operationShapeId)
              .asOperationShape()
              .get(),
            codegenContext
          );
          writer.write("raise NotImplementedError");
        }
      );

      writer.addStdlibImport(inputSymbol.getNamespace());
      writer.addStdlibImport(outputSymbol.getNamespace());
    }
  }

  /**
   * Generates abstract methods for all operations on the provided resource. This is called from a
   * resource interface to generate its abstract methods.
   *
   * @param codegenContext
   * @param resourceShape
   * @param writer
   */
  private void generateNativeWrapperFunctionDefinitionForResource(
    GenerationContext codegenContext,
    ResourceShape resourceShape,
    PythonWriter writer
  ) {
    Set<ShapeId> operationShapeIds = resourceShape.getOperations();

    for (ShapeId operationShapeId : operationShapeIds) {
      OperationShape operationShape = codegenContext
        .model()
        .expectShape(operationShapeId, OperationShape.class);

      Shape targetShapeInput = codegenContext
        .model()
        .expectShape(operationShape.getInputShape());
      SmithyNameResolver.importSmithyGeneratedTypeForShape(
        writer,
        targetShapeInput,
        codegenContext
      );

      String dafnyInput = DafnyNameResolver.getDafnyTypeForShape(
        targetShapeInput
      );
      DafnyNameResolver.importDafnyTypeForShape(
        writer,
        targetShapeInput.getId(),
        codegenContext
      );

      Shape targetShapeOutput = codegenContext
        .model()
        .expectShape(operationShape.getOutputShape());
      SmithyNameResolver.importSmithyGeneratedTypeForShape(
        writer,
        targetShapeOutput,
        codegenContext
      );

      String dafnyOutput = DafnyNameResolver.getDafnyTypeForShape(
        targetShapeOutput
      );
      DafnyNameResolver.importDafnyTypeForShape(
        writer,
        targetShapeOutput.getId(),
        codegenContext
      );

      ServiceShape serviceShape = codegenContext
        .model()
        .expectShape(codegenContext.settings().getService())
        .asServiceShape()
        .get();

      writer.addStdlibImport(
        SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
          serviceShape.getId().getNamespace(),
          codegenContext.settings()
        ) +
        ".errors",
        "_smithy_error_to_dafny_error"
      );

      writer.openBlock(
        "def $L(self, dafny_input: '$L') -> '$L':",
        "",
        operationShapeId.getName(),
        dafnyInput,
        dafnyOutput,
        () -> {
          writer.write(
            """
            ""\"
            Do not use.
            This method allows custom implementations of this interface to interact with generated code.
            ""\"
            native_input = $L(
                dafny_input
            )
            try:
                native_output = self.$L(native_input)
                dafny_output = $L(
                    native_output
                )
                return Wrappers.Result_Success(dafny_output)
            except Exception as e:
                error = _smithy_error_to_dafny_error(e)
                return Wrappers.Result_Failure(error)
            """,
            SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
              targetShapeInput.getId().getNamespace(),
              codegenContext
            ) +
            ".dafny_to_smithy." +
            SmithyNameResolver.getDafnyToSmithyFunctionNameForShape(
              targetShapeInput,
              codegenContext
            ),
            CaseUtils.toSnakeCase(operationShapeId.getName()),
            SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
              targetShapeOutput.getId().getNamespace(),
              codegenContext
            ) +
            ".smithy_to_dafny." +
            SmithyNameResolver.getSmithyToDafnyFunctionNameForShape(
              targetShapeOutput,
              codegenContext
            )
          );
          writer.addStdlibImport(
            "smithy_dafny_standard_library.internaldafny.generated",
            "Wrappers"
          );
        }
      );
    }
  }

  /**
   * Generates methods for all operations on the provided resource. The generated method takes in a
   * native type input and returns a native type output. Internally, the method will convert the
   * native type to a Dafny type, call the Dafny implementation with the Dafny type, receive a Dafny
   * type from the Dafny implementation, convert the Dafny type back to the corresponding native
   * type, and then return the native type. This is called from a concrete resource.
   *
   * @param codegenContext
   * @param resourceShape
   * @param writer
   */
  private void generateSmithyOperationFunctionDefinitionForResource(
    GenerationContext codegenContext,
    ResourceShape resourceShape,
    PythonWriter writer
  ) {
    Set<ShapeId> operationShapeIds = resourceShape.getOperations();

    for (ShapeId operationShapeId : operationShapeIds) {
      OperationShape operationShape = codegenContext
        .model()
        .expectShape(operationShapeId, OperationShape.class);
      Symbol operationSymbol = codegenContext
        .symbolProvider()
        .toSymbol(operationShape);

      Shape targetShapeInput = codegenContext
        .model()
        .expectShape(operationShape.getInputShape());
      SmithyNameResolver.importSmithyGeneratedTypeForShape(
        writer,
        targetShapeInput,
        codegenContext
      );
      // Generate code that converts the input from the Dafny type to the corresponding Smithy type
      String input = targetShapeInput.accept(
        ShapeVisitorResolver.getToDafnyShapeVisitorForShape(
          targetShapeInput,
          codegenContext,
          "param",
          writer
        )
      );
      Symbol inputSymbol = codegenContext
        .symbolProvider()
        .toSymbol(targetShapeInput);

      Shape targetShapeOutput = codegenContext
        .model()
        .expectShape(operationShape.getOutputShape());
      SmithyNameResolver.importSmithyGeneratedTypeForShape(
        writer,
        targetShapeOutput,
        codegenContext
      );
      // Generate output code converting the return value of the Dafny implementation into
      // its corresponding native-modelled type.
      String output = targetShapeOutput.accept(
        ShapeVisitorResolver.getToNativeShapeVisitorForShape(
          targetShapeOutput,
          codegenContext,
          "dafny_output.value",
          writer
        )
      );

      Symbol outputSymbol = codegenContext
        .symbolProvider()
        .toSymbol(targetShapeOutput);

      writer.openBlock(
        "def $L(self, param: '$L') -> '$L':",
        "",
        CaseUtils.toSnakeCase(operationShapeId.getName()),
        inputSymbol,
        outputSymbol,
        () -> {
          writeDocsForResourceOrInterfaceOperation(
            writer,
            operationShape,
            codegenContext
          );

          writer.write(
            "dafny_output = self._impl.$L($L)",
            operationShapeId.getName(),
            input
          );
          writer.openBlock(
            "if dafny_output.IsFailure():",
            "",
            () -> {
              // Import inline to avoid circular dependency
              writer.write(
                "from $L import $L as $L",
                //                        writer.addStdlibImport(
                // `from dependency.smithygenerated.deserialize`
                SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
                  targetShapeOutput.getId().getNamespace(),
                  codegenContext
                ) +
                ".deserialize",
                // `import _deserialize_error`
                "_deserialize_error",
                // `as dependency_deserialize_error`
                SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
                  targetShapeOutput.getId().getNamespace()
                ) +
                "_deserialize_error"
              );
              writer.write(
                "raise $L(dafny_output.error)",
                SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
                  targetShapeOutput.getId().getNamespace()
                ) +
                "_deserialize_error"
              );
            }
          );
          writer.openBlock(
            "else:",
            "",
            () -> writer.write("return $L", output)
          );
        }
      );
      writer.addStdlibImport(inputSymbol.getNamespace());
      writer.addStdlibImport(outputSymbol.getNamespace());
    }
  }

  private void writeDocsForResourceOrInterfaceClass(
    PythonWriter writer,
    ResourceShape resourceShape,
    GenerationContext context
  ) {
    if (resourceShape.getTrait(DocumentationTrait.class).isPresent()) {
      writer.writeDocs(() -> {
        resourceShape
          .getTrait(DocumentationTrait.class)
          .ifPresent(trait -> {
            writer.write(writer.formatDocs(trait.getValue()));
          });
      });
    }
  }

  private void writeDocsForResourceOrInterfaceOperation(
    PythonWriter writer,
    OperationShape operationShape,
    GenerationContext context
  ) {
    Shape inputShape = context
      .model()
      .expectShape(operationShape.getInputShape());
    Shape outputShape = context
      .model()
      .expectShape(operationShape.getOutputShape());

    if (
      operationShape.getTrait(DocumentationTrait.class).isPresent() ||
      inputShape.getTrait(DocumentationTrait.class).isPresent() ||
      outputShape.getTrait(DocumentationTrait.class).isPresent()
    ) {
      writer.writeDocs(() -> {
        operationShape
          .getTrait(DocumentationTrait.class)
          .ifPresent(trait -> {
            writer.write(writer.formatDocs(trait.getValue()));
          });
        inputShape
          .getTrait(DocumentationTrait.class)
          .ifPresent(trait -> {
            String memberDocs = writer.formatDocs(
              String.format(":param param: %s", trait.getValue())
            );
            writer.write(memberDocs);
          });
        outputShape
          .getTrait(DocumentationTrait.class)
          .ifPresent(trait -> {
            String memberDocs = writer.formatDocs(
              String.format(":returns: %s", trait.getValue())
            );
            writer.write(memberDocs);
          });
      });
    }
  }

  /**
   * Writes `as_dict` and `from_dict` methods on the resource shape. These convert the shape to/from
   * a dictionary and help with compatability across other shapes' as/from dict conversions.
   *
   * @param resource
   * @param writer
   */
  private void generateDictConvertersForResource(
    Shape resource,
    PythonWriter writer
  ) {
    writer.addStdlibImport("typing", "Dict");
    writer.addStdlibImport("typing", "Any");

    writer.write("@staticmethod");
    writer.openBlock(
      "def from_dict(d: Dict[str, Any]) -> '$L':",
      "",
      resource.getId().getName(),
      () -> {
        writer.write("return $L(d['_impl'])", resource.getId().getName());
      }
    );

    writer.openBlock(
      "def as_dict(self) -> Dict[str, Any]:",
      "",
      () -> {
        writer.write("return {'_impl': self._impl}");
      }
    );
  }
}
