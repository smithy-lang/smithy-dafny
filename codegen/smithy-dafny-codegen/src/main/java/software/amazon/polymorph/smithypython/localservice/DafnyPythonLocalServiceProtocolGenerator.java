// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice;

import static java.lang.String.format;

import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import software.amazon.polymorph.smithypython.awssdk.nameresolver.AwsSdkNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.common.shapevisitor.ShapeVisitorResolver;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolReference;
import software.amazon.smithy.codegen.core.WriterDelegator;
import software.amazon.smithy.model.shapes.*;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.python.codegen.ApplicationProtocol;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.SmithyPythonDependency;
import software.amazon.smithy.python.codegen.integration.ProtocolGenerator;
import software.amazon.smithy.utils.CodeSection;
import software.amazon.smithy.utils.SmithyUnstableApi;

@SmithyUnstableApi
public abstract class DafnyPythonLocalServiceProtocolGenerator
  implements ProtocolGenerator {

  public static ApplicationProtocol DAFNY_PYTHON_LOCAL_SERVICE_APPLICATION_PROTOCOL =
    new ApplicationProtocol(
      // Dafny localService ApplicationProtocol for Smithy clients.
      DafnyLocalServiceCodegenConstants.DAFNY_PYTHON_LOCAL_SERVICE_APPLICATION_PROTOCOL_NAME,
      SymbolReference
        .builder()
        .symbol(
          createDafnyApplicationProtocolSymbol(
            DafnyLocalServiceCodegenConstants.DAFNY_PROTOCOL_REQUEST
          )
        )
        .build(),
      SymbolReference
        .builder()
        .symbol(
          createDafnyApplicationProtocolSymbol(
            DafnyLocalServiceCodegenConstants.DAFNY_PROTOCOL_RESPONSE
          )
        )
        .build()
    );

  /**
   * Create a Symbol representing shapes inside the generated .dafny_protocol file.
   *
   * @param symbolName
   * @return
   */
  private static Symbol createDafnyApplicationProtocolSymbol(
    String symbolName
  ) {
    return Symbol
      .builder()
      .namespace(
        DafnyLocalServiceCodegenConstants.DAFNY_PROTOCOL_PYTHON_FILENAME,
        "."
      )
      .name(symbolName)
      .build();
  }

  /**
   * Creates the Dafny ApplicationProtocol object. Smithy-Python requests this object as part of the
   * ProtocolGenerator implementation.
   *
   * @return Returns the created application protocol.
   */
  @Override
  public ApplicationProtocol getApplicationProtocol() {
    return DAFNY_PYTHON_LOCAL_SERVICE_APPLICATION_PROTOCOL;
  }

  /**
   * For all operations in the model, generate a conversion method that takes in a Smithy shape and
   * converts it to a DafnyRequest.
   *
   * @param context
   */
  @Override
  public void generateRequestSerializers(GenerationContext context) {
    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    Symbol configSymbol = Symbol
      .builder()
      .name("Config")
      .namespace(
        format(
          "%s.config",
          SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
            context.settings().getService().getNamespace(),
            context
          )
        ),
        "."
      )
      .definitionFile(
        format(
          "./%s/config.py",
          SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
            context.settings().getService().getNamespace()
          )
        )
      )
      .build();

    // For each operation in the model, generate a `serialize_{operation input}` method
    for (ShapeId operationShapeId : context
      .model()
      .expectShape(context.settings().getService())
      .asServiceShape()
      .get()
      .getAllOperations()) {
      OperationShape operationShape = context
        .model()
        .expectShape(operationShapeId)
        .asOperationShape()
        .get();
      Symbol serFunction = getSerializationFunction(context, operationShape);

      // Write out the serialization operation
      delegator.useFileWriter(
        serFunction.getDefinitionFile(),
        serFunction.getNamespace(),
        writer -> {
          writer.addImport(
            DafnyLocalServiceCodegenConstants.DAFNY_PROTOCOL_PYTHON_FILENAME,
            DafnyLocalServiceCodegenConstants.DAFNY_PROTOCOL_REQUEST
          );
          writer.pushState(new RequestSerializerSection(operationShape));

          writer.write(
            """
            def $L(input, config: $T) -> $L:
                ${C|}
            """,
            serFunction.getName(),
            configSymbol,
            DafnyLocalServiceCodegenConstants.DAFNY_PROTOCOL_REQUEST,
            writer.consumer(w ->
              generateRequestSerializer(context, operationShape, w)
            )
          );
          writer.popState();
        }
      );
    }
  }

  /**
   * Generates the symbol for a serializer function for shapes of a service.
   *
   * @param context The code generation context.
   * @param shapeId The shape the serializer function is being generated for.
   * @return Returns the generated symbol.
   */
  @Override
  public Symbol getSerializationFunction(
    GenerationContext context,
    ToShapeId shapeId
  ) {
    return Symbol
      .builder()
      .name(getSerializationFunctionName(context, shapeId))
      .namespace(
        format(
          "%s.serialize",
          SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
            shapeId.toShapeId().getNamespace(),
            context
          )
        ),
        ""
      )
      .definitionFile(
        format(
          "./%s/serialize.py",
          SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
            shapeId.toShapeId().getNamespace()
          )
        )
      )
      .build();
  }

  /**
   * Generates the content of the operation request serializer.
   *
   * <p>Smithy-Python uses the word 'serialize' in this part of the code. This name stems from its
   * default HTTP-style application protocol as this code would, by default, transform
   * Smithy-modelled Python objects into serialized HTTP objects.
   *
   * <p>The Dafny plugin will not 'serialize' here, but will instead transform Smithy-modelled
   * Python objects into native Python code modelling Dafny-compiled objects.
   */
  private void generateRequestSerializer(
    GenerationContext context,
    OperationShape operation,
    PythonWriter writer
  ) {
    writer.addDependency(SmithyPythonDependency.SMITHY_PYTHON);

    // Determine conversion code from Smithy to Dafny
    Shape targetShape = context.model().expectShape(operation.getInputShape());

    String input = targetShape.accept(
      ShapeVisitorResolver.getToDafnyShapeVisitorForShape(
        targetShape,
        context,
        "input",
        writer
      )
    );

    // Write conversion method body
    writer.write(
      """
      return DafnyRequest(operation_name="$L", dafny_operation_input=$L)
      """,
      operation.getId().getName(),
      SmithyNameResolver.isUnitShape(operation.getInputShape()) ? "None" : input
    );
  }

  @Override
  public void generateResponseDeserializers(GenerationContext context) {
    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    Symbol configSymbol = Symbol
      .builder()
      .name("Config")
      .namespace(
        format(
          "%s.config",
          SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
            context.settings().getService().getNamespace(),
            context
          )
        ),
        "."
      )
      .definitionFile(
        format(
          "./%s/config.py",
          SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
            context.settings().getService().getNamespace()
          )
        )
      )
      .build();

    // For each operation in the model, generate a `deserialize_{operation input}` method
    for (ShapeId operationShapeId : context
      .model()
      .expectShape(context.settings().getService())
      .asServiceShape()
      .get()
      .getAllOperations()) {
      OperationShape operationShape = context
        .model()
        .expectShape(operationShapeId)
        .asOperationShape()
        .get();
      Symbol deserFunction = getDeserializationFunction(
        context,
        operationShape
      );

      delegator.useFileWriter(
        deserFunction.getDefinitionFile(),
        deserFunction.getNamespace(),
        writer -> {
          writer.addImport(
            DafnyLocalServiceCodegenConstants.DAFNY_PROTOCOL_PYTHON_FILENAME,
            DafnyLocalServiceCodegenConstants.DAFNY_PROTOCOL_RESPONSE
          );

          writer.pushState(new RequestDeserializerSection(operationShape));

          writer.write(
            """
            def $L(input: $L, config: $T):
              ${C|}
            """,
            deserFunction.getName(),
            DafnyLocalServiceCodegenConstants.DAFNY_PROTOCOL_RESPONSE,
            configSymbol,
            writer.consumer(w ->
              generateOperationResponseDeserializer(context, operationShape)
            )
          );

          writer.popState();
        }
      );
    }

    generateErrorResponseDeserializerSection(context);
  }

  /**
   * Generates the content of the operation response deserializer.
   *
   * <p>Smithy-Python uses the word 'deserialize' in this part of the code. This name stems from its
   * default HTTP-style application protocol as this code would, by default, transform serialized
   * HTTP objects into POJOs of Smithy-modelled objects.
   *
   * <p>The Dafny plugin will not 'deserialize' here, but will instead transform POJOs of
   * Dafny-compiled objects into POJOs of Smithy-modelled objects.
   */
  private void generateOperationResponseDeserializer(
    GenerationContext context,
    OperationShape operation
  ) {
    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    Symbol deserFunction = getDeserializationFunction(context, operation);

    delegator.useFileWriter(
      deserFunction.getDefinitionFile(),
      deserFunction.getNamespace(),
      writer -> {
        writer.pushState(new ResponseDeserializerSection(operation));

        ShapeId outputShape = operation.getOutputShape();

        if (
          context
            .model()
            .expectShape(operation.getInputShape())
            .isStructureShape() &&
          context
            .model()
            .expectShape(operation.getInputShape())
            .asStructureShape()
            .get()
            .hasTrait(PositionalTrait.class)
        ) {
          // Shapes with positional trait do not need imports
        } else {
          DafnyNameResolver.importDafnyTypeForShape(
            writer,
            outputShape,
            context
          );
        }

        // Smithy Unit shapes have no data, and do not need deserialization
        if (SmithyNameResolver.isUnitShape(outputShape)) {
          writer.write(
            """
            return None
            """
          );
        } else {
          // Determine the deserialization function
          Shape targetShape = context.model().expectShape(outputShape);
          String output = targetShape.accept(
            ShapeVisitorResolver.getToNativeShapeVisitorForShape(
              targetShape,
              context,
              "input.value",
              writer
            )
          );

          writer.write(
            """
            if input.IsFailure():
                return _deserialize_error(input.error)
            return $L
            """,
            output
          );
        }
        writer.popState();
      }
    );
  }

  @Override
  public Symbol getDeserializationFunction(
    GenerationContext context,
    ToShapeId shapeId
  ) {
    return Symbol
      .builder()
      .name(getDeserializationFunctionName(context, shapeId))
      .namespace(
        format(
          "%s.deserialize",
          SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
            shapeId.toShapeId().getNamespace(),
            context
          )
        ),
        ""
      )
      .definitionFile(
        format(
          "./%s/deserialize.py",
          SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
            shapeId.toShapeId().getNamespace()
          )
        )
      )
      .build();
  }

  /**
   * Genereal method to deserialize errors (convert from Dafny error to Smithy error
   * in the Smithy-Python client layer)
   * @param context
   */
  private void generateErrorResponseDeserializerSection(
    GenerationContext context
  ) {
    ShapeId serviceShapeId = context.settings().getService();
    ServiceShape serviceShape = context
      .model()
      .expectShape(serviceShapeId)
      .asServiceShape()
      .get();
    WriterDelegator<PythonWriter> writerDelegator = context.writerDelegator();
    String moduleName =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        context.settings().getService().getNamespace()
      );

    writerDelegator.useFileWriter(
      moduleName + "/deserialize.py",
      ".",
      writer -> {
        writer.addStdlibImport("typing", "Any");
        DafnyNameResolver.importGenericDafnyErrorTypeForNamespace(
          writer,
          serviceShape.getId().getNamespace(),
          context
        );
        writer.addImport(".errors", "ServiceError");
        writer.addImport(".errors", "OpaqueError");
        writer.addImport(".errors", "CollectionOfErrors");
        writer.addStdlibImport("_dafny");
        writer.openBlock(
          "def _deserialize_error(error: Error) -> ServiceError:",
          "",
          () -> {
            writer.write(
              """
              if error.is_Opaque:
                  return OpaqueError(obj=error.obj, alt_text=error.alt__text)
              elif error.is_CollectionOfErrors:
                  return CollectionOfErrors(
                      message=_dafny.string_of(error.message),
                      list=[_deserialize_error(dafny_e) for dafny_e in error.list],
                  )"""
            );

            // Write converters for errors modelled on this local service
            generateErrorResponseDeserializerSectionForLocalServiceErrors(
              context,
              serviceShape,
              writer
            );

            // Write delegators to dependency services' `_deserialize_error` for dependency
            // services
            generateErrorResponseDeserializerSectionForLocalServiceDependencyErrors(
              context,
              serviceShape,
              writer
            );

            // Write delegators to dependency AWS services' `_sdk_error_to_dafny_error` for
            // dependency services
            generateErrorResponseDeserializerSectionForAwsSdkDependencyErrors(
              context,
              serviceShape,
              writer
            );

            // Generate handler for unmatched Dafny Error.
            // Since we don't know anything about this Dafny Error object,
            //   just pass the Dafny Error object into the Smithy object.
            writer.write(
              """
              else:
                  return OpaqueError(obj=error, alt_text=repr(error))"""
            );
          }
        );
      }
    );
  }

  private void generateErrorResponseDeserializerSectionForLocalServiceErrors(
    GenerationContext context,
    ServiceShape serviceShape,
    PythonWriter writer
  ) {
    // Get all of this service's modelled errors
    TreeSet<ShapeId> deserializingErrorShapes = new TreeSet<ShapeId>(
      context
        .model()
        .getStructureShapesWithTrait(ErrorTrait.class)
        .stream()
        .filter(structureShape ->
          structureShape
            .getId()
            .getNamespace()
            .equals(context.settings().getService().getNamespace())
        )
        .map(Shape::getId)
        .collect(Collectors.toSet())
    );

    // Write out deserializers for this service's modelled errors
    for (ShapeId errorId : deserializingErrorShapes) {
      StructureShape error = context
        .model()
        .expectShape(errorId, StructureShape.class);
      writer.pushState(new ErrorDeserializerSection(error));

      // Import Smithy-Python modelled-error
      writer.addImport(".errors", errorId.getName());
      // Import Dafny-modelled error
      DafnyNameResolver.importDafnyTypeForError(writer, errorId, context);
      // Import generic Dafny error type
      DafnyNameResolver.importGenericDafnyErrorTypeForNamespace(
        writer,
        errorId.getNamespace(),
        context
      );
      writer.write(
        """
        elif error.is_$L:
          return $L(message=_dafny.string_of(error.message))""",
        errorId.getName(),
        errorId.getName()
      );
      writer.addStdlibImport("_dafny");
      writer.popState();
    }
  }

  private void generateErrorResponseDeserializerSectionForLocalServiceDependencyErrors(
    GenerationContext context,
    ServiceShape serviceShape,
    PythonWriter writer
  ) {
    // Generate converters for dependency services that defer to their `_deserialize_error`
    Optional<LocalServiceTrait> maybeLocalServiceTrait = serviceShape.getTrait(
      LocalServiceTrait.class
    );
    if (maybeLocalServiceTrait.isPresent()) {
      LocalServiceTrait localServiceTrait = maybeLocalServiceTrait.get();
      if (
        localServiceTrait.getDependencies() == null ||
        localServiceTrait.getDependencies().isEmpty()
      ) {
        return;
      }
      Set<ShapeId> serviceDependencyShapeIds = localServiceTrait
        .getDependencies()
        .stream()
        .filter(shapeId ->
          context.model().expectShape(shapeId).hasTrait(LocalServiceTrait.class)
        )
        .collect(Collectors.toSet());

      for (ShapeId serviceDependencyShapeId : serviceDependencyShapeIds) {
        writer.addImport(".errors", serviceDependencyShapeId.getName());

        // Import dependency `_deserialize_error` function so this service can defer to it:
        // `from dependency.smithygenerated.deserialize import _deserialize_error as
        // dependency_deserialize_error`
        writer.addImport(
          // `from dependency.smithygenerated.deserialize`
          SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
            serviceDependencyShapeId.getNamespace(),
            context
          ) +
          ".deserialize",
          // `import _deserialize_error`
          "_deserialize_error",
          // `as dependency_deserialize_error`
          SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
            serviceDependencyShapeId.getNamespace()
          ) +
          "_deserialize_error"
        );
        // Generate deserializer for dependency that defers to its `_deserialize_error`
        String serviceDependencyErrorDafnyName =
          software.amazon.polymorph.smithydafny.DafnyNameResolver.dafnyBaseModuleName(
            serviceDependencyShapeId.getNamespace()
          );

        writer.write(
          """
          elif error.is_$L:
              return $L($L(error.$L))""",
          serviceDependencyErrorDafnyName,
          serviceDependencyShapeId.getName(),
          SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
            serviceDependencyShapeId.getNamespace()
          ) +
          "_deserialize_error",
          serviceDependencyErrorDafnyName
        );
      }
    }
  }

  private void generateErrorResponseDeserializerSectionForAwsSdkDependencyErrors(
    GenerationContext context,
    ServiceShape serviceShape,
    PythonWriter writer
  ) {
    // Generate converters for dependency services that defer to their `_deserialize_error`
    Optional<LocalServiceTrait> maybeLocalServiceTrait = serviceShape.getTrait(
      LocalServiceTrait.class
    );
    if (maybeLocalServiceTrait.isPresent()) {
      LocalServiceTrait localServiceTrait = maybeLocalServiceTrait.get();
      if (
        localServiceTrait.getDependencies() == null ||
        localServiceTrait.getDependencies().isEmpty()
      ) {
        return;
      }
      Set<ShapeId> serviceDependencyShapeIds = localServiceTrait
        .getDependencies()
        .stream()
        .filter(shapeId -> AwsSdkNameResolver.isAwsSdkShape(shapeId))
        .collect(Collectors.toSet());

      for (ShapeId serviceDependencyShapeId : serviceDependencyShapeIds) {
        String code = AwsSdkNameResolver.dependencyErrorNameForService(
          context
            .model()
            .expectShape(serviceDependencyShapeId)
            .asServiceShape()
            .get()
        );
        writer.addImport(".errors", code);

        // Import dependency `_deserialize_error` function so this service can defer to it:
        // `from dependency.smithygenerated.deserialize import _deserialize_error as
        // dependency_deserialize_error`
        writer.addImport(
          // `from dependency.smithygenerated.deserialize`
          SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
            serviceDependencyShapeId.getNamespace(),
            context
          ) +
          ".shim",
          // `import _deserialize_error`
          "_sdk_error_to_dafny_error",
          // `as dependency_deserialize_error`
          SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
            serviceDependencyShapeId.getNamespace()
          ) +
          "_sdk_error_to_dafny_error"
        );
        // Generate deserializer for dependency that defers to its `_deserialize_error`
        writer.write(
          """
          elif error.is_$L:
              return $L(message=_dafny.string_of(error.$L.message))""",
          code,
          code,
          code
        );
        writer.addStdlibImport("_dafny");
      }
    }
  }

  /**
   * A section that controls writing out the entire serialization function.
   *
   * <p>By pushing and popping CodeSections, other developers can create plugins that intercept a
   * CodeSection and inject their own code here.
   *
   * @param operation The operation whose serializer is being generated.
   */
  public record RequestSerializerSection(OperationShape operation)
    implements CodeSection {}

  /**
   * A section that controls writing out the entire deserialization function.
   *
   * @param operation The operation whose serializer is being generated.
   */
  public record RequestDeserializerSection(OperationShape operation)
    implements CodeSection {}

  /**
   * A section that controls writing out the entire deserialization function for an error.
   *
   * @param error The error whose deserializer is being generated.
   */
  public record ErrorDeserializerSection(StructureShape error)
    implements CodeSection {}

  /**
   * A section that controls writing out the entire deserialization function for an operation. By
   * pushing and popping this section, we allow other developers to create plugins that intercept
   * this section and inject their own code here.
   *
   * @param operation The operation whose deserializer is being generated.
   */
  public record ResponseDeserializerSection(OperationShape operation)
    implements CodeSection {}
}
