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

package software.amazon.polymorph.smithypython;

import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import software.amazon.polymorph.smithypython.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.nameresolver.Utils;
import software.amazon.polymorph.smithypython.shapevisitor.DafnyToSmithyShapeVisitor;
import software.amazon.polymorph.smithypython.shapevisitor.SmithyToDafnyShapeVisitor;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.knowledge.TopDownIndex;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.OperationShape;
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
import software.amazon.smithy.utils.Pair;
import software.amazon.smithy.utils.SmithyUnstableApi;

/**
 *
 * <p>This will implement any handling of components outside the request
 * body and error handling.
 */
@SmithyUnstableApi
public abstract class DafnyPythonProtocolGenerator implements ProtocolGenerator {

  private final Set<Shape> serializingDocumentShapes = new TreeSet<>();
  private final Set<Shape> deserializingDocumentShapes = new TreeSet<>();

  @Override
  public ApplicationProtocol getApplicationProtocol() {
    return DafnyPythonIntegration.createDafnyApplicationProtocol();
  }

  @Override
  public void generateRequestSerializers(GenerationContext context) {
    var topDownIndex = TopDownIndex.of(context.model());
    var delegator = context.writerDelegator();
    var configSymbol = CodegenUtils.getConfigSymbol(context.settings());

    for (OperationShape operation : topDownIndex.getContainedOperations(context.settings().getService())) {
      var serFunction = getSerializationFunction(context, operation);
      var input = context.model().expectShape(operation.getInputShape());
      var inputSymbol = context.symbolProvider().toSymbol(input);

      delegator.useFileWriter(serFunction.getDefinitionFile(), serFunction.getNamespace(), writer -> {
        writer.addImport(".dafny_protocol", "DafnyRequest");
        writer.pushState(new RequestSerializerSection(operation));
        writer.write("""
                  async def $L(input: $T, config: $T) -> $L:
                      ${C|}
                  """, serFunction.getName(), inputSymbol, configSymbol,
            "DafnyRequest",
            writer.consumer(w -> generateRequestSerializer(context, operation, w)));
        writer.popState();
      });
    }
  }

  /**
   * A section that controls writing out the entire serialization function.
   *
   * @param operation The operation whose serializer is being generated.
   */
  public record RequestSerializerSection(OperationShape operation) implements CodeSection {}

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
   *
   * <p>This function has the following in scope:
   * <ul>
   *     <li>input - the operation's input</li>
   *     <li>config - the client config</li>
   * </ul>
   */
  private void generateRequestSerializer(
      GenerationContext context,
      OperationShape operation,
      PythonWriter writer
  ) {

    writer.addDependency(SmithyPythonDependency.SMITHY_PYTHON);
    // Import the Dafny type being converted to
    DafnyNameResolver.importDafnyTypeForShape(writer, operation.getInputShape());

    Shape targetShape = context.model().expectShape(operation.getInputShape());
    var input = targetShape.accept(new SmithyToDafnyShapeVisitor(
        context,
        "input",
        writer,
        false
    ));

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
    var topDownIndex = TopDownIndex.of(context.model());
    var delegator = context.writerDelegator();
    var configSymbol = CodegenUtils.getConfigSymbol(context.settings());

    var deserializingErrorShapes = new TreeSet<ShapeId>(
        context.model().getStructureShapesWithTrait(ErrorTrait.class)
            .stream()
            .filter(structureShape -> structureShape.getId().getNamespace()
                .equals(context.settings().getService().getNamespace()))
            .map(Shape::getId)
            .collect(Collectors.toSet()));

    for (OperationShape operation : topDownIndex.getContainedOperations(context.settings().getService())) {
      var deserFunction = getDeserializationFunction(context, operation);
      var output = context.model().expectShape(operation.getOutputShape());
      var outputSymbol = context.symbolProvider().toSymbol(output);

      delegator.useFileWriter(deserFunction.getDefinitionFile(), deserFunction.getNamespace(), writer -> {
        writer.addImport(".dafny_protocol", "DafnyResponse");

        writer.pushState(new RequestSerializerSection(operation));

        writer.write("""
                  async def $L(input: $L, config: $T) -> $T:
                    ${C|}
                  """, deserFunction.getName(),
            "DafnyResponse", configSymbol, outputSymbol,
            writer.consumer(w -> generateOperationResponseDeserializer(context, operation)));

        writer.popState();
      });
    }

    generateErrorResponseDeserializerSection(context, deserializingErrorShapes);
    generateDocumentBodyShapeDeserializers(context, deserializingDocumentShapes);
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
   *
   * <p>This function has the following in scope:
   * <ul>
   *     <li>dafny_response - the Dafny-level response</li>
   *     <li>config - the client config</li>
   * </ul>
   */
  private void generateOperationResponseDeserializer(
      GenerationContext context,
      OperationShape operation
  ) {
    var delegator = context.writerDelegator();
    var deserFunction = getDeserializationFunction(context, operation);
    delegator.useFileWriter(deserFunction.getDefinitionFile(), deserFunction.getNamespace(), writer -> {
      writer.pushState(new ResponseDeserializerSection(operation));

      ShapeId outputShape = operation.getOutputShape();
      DafnyNameResolver.importDafnyTypeForShape(writer, outputShape);

      // TODO: If there is no output... how can there be an error?
      if (Utils.isUnitShape(outputShape)) {
        writer.write("""
          return None
          """);
      } else {
        Shape targetShape = context.model().expectShape(outputShape);
        var output = targetShape.accept(new DafnyToSmithyShapeVisitor(
            context,
            "input.value",
            writer,
            false
        ));

        writer.write("""
          if input.IsFailure():
            return await _deserialize_error(input.error)
          return $L
          """, output);
      }
      writer.popState();
    });
  }

  /**
   * A section that controls writing out the entire deserialization function for an operation.
   *
   * @param operation The operation whose deserializer is being generated.
   */
  public record ResponseDeserializerSection(OperationShape operation) implements CodeSection {}

  // TODO: CodeSection-ize this?
  private void generateErrorResponseDeserializerSection(
      GenerationContext context,
      TreeSet<ShapeId> deserializingErrorShapes)
  {
    // I need to store a map from deserFunction metadata -> Set<errorId>
    // Such that for a given set of metadata (i.e. a given file),
    // I have all of the errors I need to write to that file
    // TODO: Less brittle datatype than Pair
    Map<Pair<String, String>, List<ShapeId>> deserFunctionToErrorsMap = new HashMap<>();
    for (ShapeId errorId : deserializingErrorShapes) {
      var error = context.model().expectShape(errorId, StructureShape.class);
      var deserFunction = getErrorDeserializationFunction(context, error);
      deserFunction.getDefinitionFile();
      Pair<String, String> deserFunctionMetadata = Pair.of(deserFunction.getDefinitionFile(), deserFunction.getNamespace());

      if (deserFunctionToErrorsMap.containsKey(deserFunction)) {
        List<ShapeId> oldList = deserFunctionToErrorsMap.get(deserFunction);
        oldList.add(errorId);
        deserFunctionToErrorsMap.put(
            deserFunctionMetadata,
            oldList
        );
      } else {
        deserFunctionToErrorsMap.put(
            deserFunctionMetadata,
            Arrays.asList(errorId)
        );
      }
    }

    for (Pair<String, String> deserFunctionMetadata : deserFunctionToErrorsMap.keySet()) {
      var delegator = context.writerDelegator();
      delegator.useFileWriter(deserFunctionMetadata.getLeft(), deserFunctionMetadata.getRight(), writer -> {

        writer.addStdlibImport("typing", "Any");
        // TODO: Is this generated if there are no modelled errors...?
        writer.addImport(".errors", "ServiceError");
        writer.addImport(".errors", "OpaqueError");
        writer.addImport(".errors", "CollectionOfErrors");
        writer.write("""
                async def _deserialize_error(
                    error: Error
                ) -> ServiceError:
                  if error.is_Opaque:
                    return OpaqueError(obj=error.obj)
                  if error.is_CollectionOfErrors:
                    return CollectionOfErrors(message=error.message, list=error.list)"""
          );

        for (ShapeId errorId : deserFunctionToErrorsMap.get(deserFunctionMetadata)) {
          var error = context.model().expectShape(errorId, StructureShape.class);
          writer.pushState(new ErrorDeserializerSection(error));

          // Import Smithy-Python modelled-error
          writer.addImport(".errors", errorId.getName());
          // Import Dafny-modelled error
          DafnyNameResolver.importDafnyTypeForError(writer, errorId);
          // Import generic Dafny error type
          DafnyNameResolver.importGenericDafnyErrorTypeForNamespace(writer, errorId.getNamespace());
          writer.write("""
                  if error.is_$L:
                    return $L(message=error.message)
                """, errorId.getName(), errorId.getName()
          );
          writer.popState();
        }
      });
    }
  }

  /**
   * A section that controls writing out the entire deserialization function for an error.
   *
   * @param error The error whose deserializer is being generated.
   */
  public record ErrorDeserializerSection(StructureShape error) implements CodeSection {}

  /**
   * Generates deserialization functions for shapes in the given set.
   *
   * <p>These are the functions that deserializeDocumentBody will call out to.
   *
   * @param context The generation context.
   * @param shapes The shapes to generate deserialization for.
   */
  protected abstract void generateDocumentBodyShapeDeserializers(
      GenerationContext context,
      Set<Shape> shapes
  );

}
