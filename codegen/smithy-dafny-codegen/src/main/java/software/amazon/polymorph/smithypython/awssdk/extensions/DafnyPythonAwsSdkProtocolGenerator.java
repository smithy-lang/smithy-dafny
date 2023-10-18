/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *   http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

package software.amazon.polymorph.smithypython.awssdk.extensions;

import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import software.amazon.polymorph.smithypython.Constants;
import software.amazon.polymorph.smithypython.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.nameresolver.Utils;
import software.amazon.polymorph.smithypython.shapevisitor.DafnyToSmithyShapeVisitor;
import software.amazon.polymorph.smithypython.shapevisitor.SmithyToDafnyShapeVisitor;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolReference;
import software.amazon.smithy.codegen.core.WriterDelegator;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.python.codegen.ApplicationProtocol;
import software.amazon.smithy.python.codegen.CodegenUtils;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.SmithyPythonDependency;
import software.amazon.smithy.python.codegen.integration.ProtocolGenerator;
import software.amazon.smithy.utils.CodeSection;
import software.amazon.smithy.utils.SmithyUnstableApi;

/**
 * This will implement any handling of components outside the request
 * body and error handling.
 */
@SmithyUnstableApi
public abstract class DafnyPythonAwsSdkProtocolGenerator implements ProtocolGenerator {

  /**
   * Create a Symbol representing shapes inside the generated .dafny_protocol file.
   * @param symbolName
   * @return
   */
  private static Symbol createDafnyApplicationProtocolSymbol(String symbolName) {
    return Symbol.builder()
        .namespace(Constants.DAFNY_PROTOCOL_PYTHON_FILENAME, ".")
        .name(symbolName)
        .build();
  }

  /**
   * Creates the Dafny ApplicationProtocol object.
   * Smithy-Python requests this object as part of the ProtocolGenerator implementation.
   *
   * @return Returns the created application protocol.
   */
  @Override
  public ApplicationProtocol getApplicationProtocol() {
    return new ApplicationProtocol(
        // Define the `dafny` ApplicationProtocol.
        // This protocol's request and response shapes are defined in DafnyProtocolFileWriter.
        "dafny-aws-sdk",
        SymbolReference.builder()
            .symbol(createDafnyApplicationProtocolSymbol(Constants.DAFNY_PROTOCOL_REQUEST))
            .build(),
        SymbolReference.builder()
            .symbol(createDafnyApplicationProtocolSymbol(Constants.DAFNY_PROTOCOL_RESPONSE))
            .build()
    );
  }

  /**
   * A section that controls writing out the entire serialization function.
   *
   * By pushing and popping CodeSections, other developers
   *   can create plugins that intercept a CodeSection and inject their
   *   own code here.
   *
   * @param operation The operation whose serializer is being generated.
   */
  public record RequestSerializerSection(OperationShape operation) implements CodeSection {}

  /**
   * A section that controls writing out the entire deserialization function.
   *
   * @param operation The operation whose serializer is being generated.
   */
  public record RequestDeserializerSection(OperationShape operation) implements CodeSection {}

  /**
   * A section that controls writing out the entire deserialization function for an error.
   *
   * @param error The error whose deserializer is being generated.
   */
  public record ErrorDeserializerSection(StructureShape error) implements CodeSection {}


  /**
   * For all operations in the model, generate a conversion method
   *   that takes in a Smithy shape and converts it to a DafnyRequest.
   * @param context
   */
  @Override
  public void generateRequestSerializers(GenerationContext context) {
    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    Symbol configSymbol = CodegenUtils.getConfigSymbol(context.settings());

    // For each operation in the model, generate a `serialize_{operation input}` method
    for (OperationShape operation : context.model().getOperationShapes()) {
      Symbol serFunction = getSerializationFunction(context, operation);
      Shape input = context.model().expectShape(operation.getInputShape());
      Symbol inputSymbol = SmithyNameResolver.generateSmithyDafnySymbolForShape(context, input);

      // Write out the serialization operation
      delegator.useFileWriter(serFunction.getDefinitionFile(), serFunction.getNamespace(), writer -> {
        writer.addImport(Constants.DAFNY_PROTOCOL_PYTHON_FILENAME, Constants.DAFNY_PROTOCOL_REQUEST);
        writer.pushState(new RequestSerializerSection(operation));
        writer.write("""
            async def $L(input: $T, config: $T) -> $L:
                ${C|}
            """,
            serFunction.getName(),
            inputSymbol,
            configSymbol,
            Constants.DAFNY_PROTOCOL_REQUEST,
            writer.consumer(w -> generateRequestSerializer(context, operation, w)));
        writer.popState();
      });
    }
  }

  /**
   * Generates the content of the operation request serializer.
   *
   * Smithy-Python uses the word 'serialize' in this part of the code.
   * This name stems from its default HTTP-style application protocol
   * as this code would, by default, transform POJOs of Smithy-modelled objects
   * into serialized HTTP objects.
   *
   * The Dafny plugin will not 'serialize' here, but will instead
   * transform POJOs of Smithy-modelled objects
   * into POJOs of Dafny-compiled objects.
   */
  private void generateRequestSerializer(
      GenerationContext context,
      OperationShape operation,
      PythonWriter writer
  ) {

    writer.addDependency(SmithyPythonDependency.SMITHY_PYTHON);
    // Import the Dafny type being converted to
    DafnyNameResolver.importDafnyTypeForShape(writer, operation.getInputShape(), context);

    // Determine conversion code from Smithy to Dafny
    Shape targetShape = context.model().expectShape(operation.getInputShape());
    String input = targetShape.accept(new SmithyToDafnyShapeVisitor(
        context,
        "input",
        writer,
        "serialize"
    ));

    // Write conversion method body
    writer.write(
          """
          return DafnyRequest(operation_name="$L", dafny_operation_input=$L)
          """,
        operation.getId().getName(),
        Utils.isUnitShape(operation.getInputShape()) ? "None" : input
    );
  }

  @Override
  public void generateResponseDeserializers(GenerationContext context) {
    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    Symbol configSymbol = CodegenUtils.getConfigSymbol(context.settings());

    // For each operation in the model, generate a `deserialize_{operation input}` method
    for (OperationShape operation : context.model().getOperationShapes()) {
      Symbol deserFunction = getDeserializationFunction(context, operation);
      Shape output = context.model().expectShape(operation.getOutputShape());
      Symbol outputSymbol = SmithyNameResolver.generateSmithyDafnySymbolForShape(context, output);

      delegator.useFileWriter(deserFunction.getDefinitionFile(), deserFunction.getNamespace(), writer -> {
        writer.addImport(Constants.DAFNY_PROTOCOL_PYTHON_FILENAME, Constants.DAFNY_PROTOCOL_RESPONSE);

        writer.pushState(new RequestDeserializerSection(operation));

        writer.write("""
            async def $L(input: $L, config: $T) -> $T:
              ${C|}
            """,
            deserFunction.getName(),
            Constants.DAFNY_PROTOCOL_RESPONSE,
            configSymbol,
            outputSymbol,
            writer.consumer(w -> generateOperationResponseDeserializer(context, operation))
        );

        writer.popState();
      });
    }

    generateErrorResponseDeserializerSection(context);
  }

  /**
   * Generates the content of the operation response deserializer.
   *
   * Smithy-Python uses the word 'deserialize' in this part of the code.
   * This name stems from its default HTTP-style application protocol
   * as this code would, by default, transform serialized HTTP objects
   * into POJOs of Smithy-modelled objects.
   *
   * The Dafny plugin will not 'deserialize' here, but will instead
   * transform POJOs of Dafny-compiled objects
   * into POJOs of Smithy-modelled objects.
   */
  private void generateOperationResponseDeserializer(
      GenerationContext context,
      OperationShape operation
  ) {
    WriterDelegator<PythonWriter> delegator = context.writerDelegator();
    Symbol deserFunction = getDeserializationFunction(context, operation);

    delegator.useFileWriter(deserFunction.getDefinitionFile(), deserFunction.getNamespace(), writer -> {
      writer.pushState(new ResponseDeserializerSection(operation));

      ShapeId outputShape = operation.getOutputShape();
      DafnyNameResolver.importDafnyTypeForShape(writer, outputShape, context);

      // Smithy Unit shapes have no data, and do not need deserialization
      if (Utils.isUnitShape(outputShape)) {
        writer.write("""
          return None
          """);
      } else {
        // Determine the deserialization function
        Shape targetShape = context.model().expectShape(outputShape);
        String output = targetShape.accept(new DafnyToSmithyShapeVisitor(
            context,
            "input.value",
            writer,
            "deserialize"
        ));

        writer.write("""
          if input.IsFailure():
            return await _deserialize_error(input.error)
          # Import dafny_to_smithy at runtime to prevent introducing circular dependency on deserialize file.
          from . import dafny_to_smithy
          return dafny_to_smithy.$L
          """,
          output
        );
      }
      writer.popState();
    });
  }

  /**
   * A section that controls writing out the entire deserialization function for an operation.
   * By pushing and popping this section, we allow other developers
   *   to create plugins that intercept this section and inject their
   *   own code here.
   *
   * @param operation The operation whose deserializer is being generated.
   */
  public record ResponseDeserializerSection(OperationShape operation) implements CodeSection {}

  private void generateErrorResponseDeserializerSection(GenerationContext context) {
    ShapeId serviceShapeId = context.settings().getService();
    ServiceShape serviceShape = context.model().expectShape(serviceShapeId).asServiceShape().get();
    WriterDelegator<PythonWriter> writerDelegator = context.writerDelegator();
    String moduleName = context.settings().getModuleName();

    writerDelegator.useFileWriter(moduleName + "/deserialize.py", ".", writer -> {
      writer.addStdlibImport("typing", "Any");
      DafnyNameResolver.importGenericDafnyErrorTypeForNamespace(writer,
          serviceShape.getId().getNamespace());
      writer.addImport(".errors", "ServiceError");
      writer.addImport(".errors", "OpaqueError");
      writer.addImport(".errors", "CollectionOfErrors");
      writer.openBlock(
          "async def _deserialize_error(error: Error) -> ServiceError:",
          "",
          () -> {
            writer.write("""
                if error.is_Opaque:
                  return OpaqueError(obj=error.obj)
                elif error.is_CollectionOfErrors:
                  return CollectionOfErrors(message=error.message, list=error.list)""");

                // Write converters for errors modelled on this local service
                generateErrorResponseDeserializerSectionForLocalServiceErrors(context, serviceShape, writer);

                // Write delegators to dependency services' `_deserialize_error` for dependency services
                generateErrorResponseDeserializerSectionForLocalServiceDependencyErrors(context, serviceShape, writer);

                // Generate handler for unmatched Dafny Error.
                // Since we don't know anything about this Dafny Error object,
                //   just pass the Dafny Error object into the Smithy object.
                writer.write("""
                    else:
                        return OpaqueError(obj=error)"""
                );
          });

    });
  }

  private void generateErrorResponseDeserializerSectionForLocalServiceErrors(GenerationContext context,
      ServiceShape serviceShape, PythonWriter writer) {

    // Get all of this service's modelled errors
    TreeSet<ShapeId> deserializingErrorShapes = new TreeSet<ShapeId>(
        context.model().getStructureShapesWithTrait(ErrorTrait.class)
            .stream()
            .filter(structureShape -> structureShape.getId().getNamespace()
                .equals(context.settings().getService().getNamespace()))
            .map(Shape::getId)
            .collect(Collectors.toSet()));

    // Write out deserializers for this service's modelled errors
    for (ShapeId errorId : deserializingErrorShapes) {
      StructureShape error = context.model().expectShape(errorId, StructureShape.class);
      writer.pushState(new ErrorDeserializerSection(error));

      // Import Smithy-Python modelled-error
      writer.addImport(".errors", errorId.getName());
      // Import Dafny-modelled error
      DafnyNameResolver.importDafnyTypeForError(writer, errorId, context);
      // Import generic Dafny error type
      DafnyNameResolver.importGenericDafnyErrorTypeForNamespace(writer, errorId.getNamespace());
      writer.write(
          """
            elif error.is_$L:
              return $L(message=error.message)""",
          errorId.getName(),
          errorId.getName()
      );
      writer.popState();
    }
  }

  private void generateErrorResponseDeserializerSectionForLocalServiceDependencyErrors(GenerationContext context,
      ServiceShape serviceShape, PythonWriter writer) {

    // Generate converters for dependency services that defer to their `_deserialize_error`
    Optional<LocalServiceTrait> maybeLocalServiceTrait = serviceShape.getTrait(LocalServiceTrait.class);
    if (maybeLocalServiceTrait.isPresent()) {
      LocalServiceTrait localServiceTrait = maybeLocalServiceTrait.get();
      Set<ShapeId> serviceDependencyShapeIds = localServiceTrait.getDependencies();
      if (serviceDependencyShapeIds != null) {
        for (ShapeId serviceDependencyShapeId : serviceDependencyShapeIds) {
          writer.addImport(".errors", serviceDependencyShapeId.getName());

          // Import dependency `_deserialize_error` function so this service can defer to it:
          // `from dependency.smithygenerated.deserialize import _deserialize_error as dependency_deserialize_error`
          writer.addImport(
              // `from dependency.smithygenerated.deserialize`
              SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(serviceDependencyShapeId.getNamespace())
                  + ".smithygenerated.deserialize",
              // `import _deserialize_error`
              "_deserialize_error",
              // `as dependency_deserialize_error`
              SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(serviceDependencyShapeId.getNamespace())
                  + "_deserialize_error"
          );
          // Generate deserializer for dependency that defers to its `_deserialize_error`
          writer.write(
              """
              elif error.is_$L:
                  return $L(await $L(error.$L))""",
              serviceDependencyShapeId.getName(), serviceDependencyShapeId.getName(),
              SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(serviceDependencyShapeId.getNamespace())
                  + "_deserialize_error",
              serviceDependencyShapeId.getName()
          );
        }
      }
    }
  }
}
