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

import static software.amazon.smithy.model.traits.TimestampFormatTrait.Format;

import java.util.Locale;
import java.util.Set;
import java.util.TreeSet;
import software.amazon.smithy.codegen.core.CodegenException;
import software.amazon.smithy.model.knowledge.HttpBinding.Location;
import software.amazon.smithy.model.knowledge.TopDownIndex;
import software.amazon.smithy.model.shapes.BigDecimalShape;
import software.amazon.smithy.model.shapes.BigIntegerShape;
import software.amazon.smithy.model.shapes.BlobShape;
import software.amazon.smithy.model.shapes.BooleanShape;
import software.amazon.smithy.model.shapes.ByteShape;
import software.amazon.smithy.model.shapes.DoubleShape;
import software.amazon.smithy.model.shapes.FloatShape;
import software.amazon.smithy.model.shapes.IntegerShape;
import software.amazon.smithy.model.shapes.LongShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ShapeVisitor;
import software.amazon.smithy.model.shapes.ShortShape;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.TimestampShape;
import software.amazon.smithy.python.codegen.ApplicationProtocol;
import software.amazon.smithy.python.codegen.CodegenUtils;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.SmithyPythonDependency;
import software.amazon.smithy.python.codegen.integration.ProtocolGenerator;
import software.amazon.smithy.utils.CodeSection;
import software.amazon.smithy.utils.SmithyUnstableApi;
import software.amazon.smithy.utils.StringUtils;

/**
 *
 * <p>This will implement any handling of components outside the request
 * body and error handling.
 */
// TODO: Naming of DafnyProtocolGenerator?
@SmithyUnstableApi
public abstract class DafnyProtocolGenerator implements ProtocolGenerator {

  private final Set<Shape> serializingDocumentShapes = new TreeSet<>();
  private final Set<Shape> deserializingDocumentShapes = new TreeSet<>();

  @Override
  public ApplicationProtocol getApplicationProtocol() {
    return DafnyIntegration.createDafnyApplicationProtocol();
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
        writer.pushState(new RequestSerializerSection(operation));
        // TODO: nameresolver
        writer.write("""
                    async def $L(input: $T, config: $T) -> Dafny$T:
                        ${C|}
                    """, serFunction.getName(), inputSymbol, configSymbol, inputSymbol,
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
    ServiceShape serviceShape = ( ServiceShape) context.model().getServiceShapes().toArray()[0];
    String serviceName = serviceShape.getId().getName();

    // TODO: nameresolver
    String typesModulePrelude = operation.getInputShape().getNamespace().toLowerCase(Locale.ROOT) + ".internaldafny.types";
    String inputName = operation.getInputShape().getName();
    writer.addImport(typesModulePrelude, inputName + "_" + inputName, "Dafny" + inputName);

    System.out.println("ytoyo");
    System.out.println(operation.getInput());

    Shape targetShape = context.model().expectShape(operation.getInputShape());
    // TODO: This isn't right... need to support >1 member in structure
    MemberShape member = targetShape.getMember("value").get();
    System.out.println(targetShape);
    System.out.println(targetShape.getMemberNames());
    var input = targetShape.accept(new DafnyMemberSerVisitor(
        context,
        writer,
        "input",
        member
    ));

        /*
        return ("$L", $L(
         */

    // value=input.value

    writer.write("""
            return ("$L", $L($L))
            """, operation.getId().getName(), "Dafny" + inputName, input
        );
  }

  @Override
  public void generateResponseDeserializers(GenerationContext context) {
    var topDownIndex = TopDownIndex.of(context.model());
    var service = context.settings().getService(context.model());
    var deserializingErrorShapes = new TreeSet<ShapeId>();
    var delegator = context.writerDelegator();
    var configSymbol = CodegenUtils.getConfigSymbol(context.settings());

    for (OperationShape operation : topDownIndex.getContainedOperations(context.settings().getService())) {
      deserializingErrorShapes.addAll(operation.getErrors(service));

      var deserFunction = getDeserializationFunction(context, operation);
      var output = context.model().expectShape(operation.getOutputShape());
      var outputSymbol = context.symbolProvider().toSymbol(output);
      delegator.useFileWriter(deserFunction.getDefinitionFile(), deserFunction.getNamespace(), writer -> {
        writer.pushState(new RequestSerializerSection(operation));

        writer.write("""
                    async def $L(input: Dafny$T, config: $T) -> $T:
                      ${C|}
                    """, deserFunction.getName(), outputSymbol, configSymbol, outputSymbol,
            writer.consumer(w -> generateOperationResponseDeserializer(context, operation)));
        writer.popState();
      });
    }

    for (ShapeId errorId : deserializingErrorShapes) {
      var error = context.model().expectShape(errorId, StructureShape.class);
      generateErrorResponseDeserializer(context, error);
    }
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

      // TODO: nameresolver
      String typesModulePrelude = operation.getOutputShape().getNamespace().toLowerCase(Locale.ROOT)  + ".internaldafny.types";
      String outputName = operation.getOutputShape().getName();
      writer.addImport(typesModulePrelude, outputName + "_" + outputName, "Dafny" + outputName);

      Shape targetShape = context.model().expectShape(operation.getOutputShape());
      // TODO: support >1 member in structure
      MemberShape member = targetShape.getMember("value").get();
      var output = targetShape.accept(new DafnyMemberDeserVisitor(
          context,
          writer,
          "input",
          member
      ));

      writer.write("""
return $L($L)
      """, outputName, output);
      writer.popState();
    });
  }

  /**
   * A section that controls writing out the entire deserialization function for an operation.
   *
   * @param operation The operation whose deserializer is being generated.
   */
  public record ResponseDeserializerSection(OperationShape operation) implements CodeSection {}

  private void generateErrorResponseDeserializer(GenerationContext context, StructureShape error) {
//    throw new UnsupportedOperationException("Error generation not supported");
    var deserFunction = getErrorDeserializationFunction(context, error);
    var errorSymbol = context.symbolProvider().toSymbol(error);
    var delegator = context.writerDelegator();
    var transportResponse = context.applicationProtocol().responseType();
    var configSymbol = CodegenUtils.getConfigSymbol(context.settings());

    delegator.useFileWriter(deserFunction.getDefinitionFile(), deserFunction.getNamespace(), writer -> {
      writer.pushState(new ErrorDeserializerSection(error));
      writer.addStdlibImport("typing", "Any");
      writer.write("""
                # Need to convert Dafny types' Error_SimpleErrorsException to .models' SimpleErrorsException
                # Actually! This is Wrappers_Compile.Failure(Error_SimpleErrorsException)
                # so unwrapping it prolly looks like
                # 
                async def $L(
                    http_response: $T,
                    config: $T,
                    parsed_body: dict[str, Document]| None,
                    default_message: str,
                ) -> $T:
                    kwargs: dict[str, Any] = {"message": default_message}

                """, deserFunction.getName(), transportResponse, configSymbol, errorSymbol);
      writer.popState();
    });
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

  /**
   * Given context and a source of data, generate an input value provider for the
   * shape. This may use native types or invoke complex type serializers to
   * manipulate the dataSource into the proper input content.
   */
  // TODO: Naming of DafnyMemberSerVisitor?
  private static class DafnyMemberSerVisitor extends ShapeVisitor.Default<String> {
    private final GenerationContext context;
    private final PythonWriter writer;
    private final String dataSource;
    private final MemberShape member;

    /**
     * @param context The generation context.
     * @param writer The writer to add dependencies to.
     * @param dataSource The in-code location of the data to provide an output of
     *                   ({@code input.foo}, {@code entry}, etc.)
     * @param member The member that points to the value being provided.
     */
    DafnyMemberSerVisitor(
        GenerationContext context,
        PythonWriter writer,
        String dataSource,
        MemberShape member
    ) {
      this.context = context;
      this.writer = writer;
      this.dataSource = dataSource;
      this.member = member;
    }

    @Override
    protected String getDefault(Shape shape) {
      var protocolName = context.protocolGenerator().getName();
      throw new CodegenException(String.format(
          "Unsupported conversion of %s to %s in %s using the %s protocol",
          member.getMemberName(), shape.getType(), member.getContainer(), protocolName));
    }

    @Override
    public String blobShape(BlobShape shape) {
      return getDefault(shape);
    }

    @Override
    public String structureShape(StructureShape shape) {
      System.out.println("structureShape");
      String out = "";
      // TODO: Change fstring to support >1 shape
      if (shape.getMemberNames().size() > 1) {
        throw new UnsupportedOperationException("StructureShapes with >1 value not supported");
      }
      for (String memberName : shape.getMemberNames()) {
        out += "%1$s=%2$s.%1$s".formatted(memberName, dataSource);
      }
      return out;
    }

    @Override
    public String booleanShape(BooleanShape shape) {
      return getDefault(shape);
    }

    @Override
    public String stringShape(StringShape shape) {
      return getDefault(shape);
    }

    @Override
    public String byteShape(ByteShape shape) {
      return getDefault(shape);
    }

    @Override
    public String shortShape(ShortShape shape) {
      return getDefault(shape);
    }

    @Override
    public String integerShape(IntegerShape shape) {
      return getDefault(shape);
    }

    @Override
    public String longShape(LongShape shape) {
      return getDefault(shape);
    }

    @Override
    public String bigIntegerShape(BigIntegerShape shape) {
      return getDefault(shape);
    }

    @Override
    public String floatShape(FloatShape shape) {
      return getDefault(shape);
    }

    @Override
    public String doubleShape(DoubleShape shape) {
      return getDefault(shape);
    }

    @Override
    public String bigDecimalShape(BigDecimalShape shape) {
      return getDefault(shape);
    }

    @Override
    public String timestampShape(TimestampShape shape) {
      return getDefault(shape);
    }
  }

  /**
   * Given context and a source of data, generate an output value provider for the
   * shape. This may use native types (like generating a datetime for timestamps)
   * converters (like a b64decode) or invoke complex type deserializers to
   * manipulate the dataSource into the proper output content.
   */
  // TODO: Naming of DafnyMemberDeserVisitor?
  private static class DafnyMemberDeserVisitor extends ShapeVisitor.Default<String> {

    private final GenerationContext context;
    private final PythonWriter writer;
    private final String dataSource;
    private final MemberShape member;

    /**
     * @param context The generation context.
     * @param writer The writer to add dependencies to.
     * @param dataSource The in-code location of the data to provide an output of
     *                   ({@code output.foo}, {@code entry}, etc.)
     * @param member The member that points to the value being provided.
     */
    DafnyMemberDeserVisitor(
        GenerationContext context,
        PythonWriter writer,
        String dataSource,
        MemberShape member
    ) {
      this.context = context;
      this.writer = writer;
      this.dataSource = dataSource;
      this.member = member;
    }

    @Override
    protected String getDefault(Shape shape) {
      var protocolName = context.protocolGenerator().getName();
      throw new CodegenException(String.format(
          "Unsupported conversion of %s to %s in %s using the %s protocol",
          member.getMemberName(), shape.getType(), member.getContainer(), protocolName));
    }

    @Override
    public String blobShape(BlobShape shape) {
      return getDefault(shape);
    }

    @Override
    public String structureShape(StructureShape shape) {
      System.out.println("structureShape deser");
      String out = "";
      // TODO: Change fstring to support >1 shape
      if (shape.getMemberNames().size() > 1) {
        throw new UnsupportedOperationException("StructureShapes with >1 value not supported");
      }
      for (String memberName : shape.getMemberNames()) {
        // TODO: Investigate what this should be... one of these is accessing a Wrappers_Compile...
        out += "%1$s=%2$s.value.%1$s".formatted(memberName, dataSource);
      }
      return out;
    }

    @Override
    public String booleanShape(BooleanShape shape) {
      return getDefault(shape);
    }

    @Override
    public String stringShape(StringShape shape) {
      return getDefault(shape);
    }

    @Override
    public String byteShape(ByteShape shape) {
      return getDefault(shape);
    }

    @Override
    public String shortShape(ShortShape shape) {
      return getDefault(shape);
    }

    @Override
    public String integerShape(IntegerShape shape) {
      return getDefault(shape);
    }

    @Override
    public String longShape(LongShape shape) {
      return getDefault(shape);
    }

    @Override
    public String bigIntegerShape(BigIntegerShape shape) {
      return getDefault(shape);
    }

    @Override
    public String floatShape(FloatShape shape) {
      return getDefault(shape);
    }

    @Override
    public String doubleShape(DoubleShape shape) {
      return getDefault(shape);
    }

    @Override
    public String bigDecimalShape(BigDecimalShape shape) {
      return getDefault(shape);
    }

    @Override
    public String timestampShape(TimestampShape shape) {
      return getDefault(shape);
    }
  }
}
