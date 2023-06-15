package software.amazon.smithy.dafny.python;/*
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


import static java.lang.String.format;
import static software.amazon.smithy.model.knowledge.HttpBinding.Location.HEADER;
import static software.amazon.smithy.model.knowledge.HttpBinding.Location.PAYLOAD;
import static software.amazon.smithy.model.knowledge.HttpBinding.Location.PREFIX_HEADERS;
import static software.amazon.smithy.model.traits.TimestampFormatTrait.Format;

import java.util.List;
import java.util.Set;
import java.util.TreeSet;
import software.amazon.smithy.codegen.core.CodegenException;
import software.amazon.smithy.model.knowledge.HttpBinding.Location;
import software.amazon.smithy.model.knowledge.HttpBindingIndex;
import software.amazon.smithy.model.knowledge.TopDownIndex;
import software.amazon.smithy.model.shapes.BigDecimalShape;
import software.amazon.smithy.model.shapes.BigIntegerShape;
import software.amazon.smithy.model.shapes.BlobShape;
import software.amazon.smithy.model.shapes.BooleanShape;
import software.amazon.smithy.model.shapes.ByteShape;
import software.amazon.smithy.model.shapes.DoubleShape;
import software.amazon.smithy.model.shapes.FloatShape;
import software.amazon.smithy.model.shapes.IntegerShape;
import software.amazon.smithy.model.shapes.ListShape;
import software.amazon.smithy.model.shapes.LongShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ShapeVisitor;
import software.amazon.smithy.model.shapes.ShortShape;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.TimestampShape;
import software.amazon.smithy.model.traits.MediaTypeTrait;
import software.amazon.smithy.model.traits.StreamingTrait;
import software.amazon.smithy.python.codegen.ApplicationProtocol;
import software.amazon.smithy.python.codegen.CodegenUtils;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.SmithyPythonDependency;
import software.amazon.smithy.python.codegen.integration.ProtocolGenerator;
import software.amazon.smithy.utils.CodeInterceptor;
import software.amazon.smithy.utils.CodeSection;
import software.amazon.smithy.utils.SmithyUnstableApi;
/*
dafny \
    -vcsCores:2 \
    -compileTarget:java\
    -spillTargetCode:3 \
    -compile:0 \
    -useRuntimeLib \
    -out runtimes/java \
    ./src/Index.dfy \
    -library:$(PROJECT_ROOT)/dafny-dependencies/StandardLibrary/src/Index.dfy \
    $(patsubst %, -library:$(PROJECT_ROOT)/%/src/Index.dfy, $(LIBRARIES))

 */

/**
 * Abstract implementation useful for all protocols that use HTTP bindings.
 *
 * <p>This will implement any handling of components outside the request
 * body and error handling.
 */
@SmithyUnstableApi
public abstract class DafnyProtocolGenerator implements ProtocolGenerator {

  private final Set<Shape> serializingDocumentShapes = new TreeSet<>();
  private final Set<Shape> deserializingDocumentShapes = new TreeSet<>();

  @Override
  public ApplicationProtocol getApplicationProtocol() {
    return DafnyTestIntegration.createDafnyApplicationProtocol();
  }

  @Override
  public void generateRequestSerializers(GenerationContext context) {
    var topDownIndex = TopDownIndex.of(context.model());
    var delegator = context.writerDelegator();
    var configSymbol = CodegenUtils.getConfigSymbol(context.settings());
    // I beLIEVE transportRequest needs to be the output shape
    // for requestSeralizers this is a dafnyType
    // i.e. the operation output...?
    // no... the operation output is... not... this...
    // Oh, ok: input is GetBooleanInput, output is GetBooleanOutput...
    // OH, duhDOY. I am looking at the Smithy model. Smithy model dgaf about the Dafny stuff.
    // I need to hardcode the Dafny stuff!
    // i.e. DafnyNameResolver... one day. For now, name = "Dafny"+input.
    // Actually, for now: hardcoded DafnyGetBooleanInput.
    var transportRequest = context.applicationProtocol().requestType();
    for (OperationShape operation : topDownIndex.getContainedOperations(context.settings().getService())) {
      var serFunction = getSerializationFunction(context, operation);
      var input = context.model().expectShape(operation.getInputShape());
      var inputSymbol = context.symbolProvider().toSymbol(input);
      var output = context.model().expectShape(operation.getOutputShape());
      var outputSymbol = context.symbolProvider().toSymbol(output);
      delegator.useFileWriter(serFunction.getDefinitionFile(), serFunction.getNamespace(), writer -> {
        writer.pushState(new RequestSerializerSection(operation));
        writer.write("""
                    async def $L(input: $T, config: $T) -> DafnyGetBooleanInput:
                        ${C|}
                    """, serFunction.getName(), inputSymbol, configSymbol,
            writer.consumer(w -> generateRequestSerializer(context, operation, w)));
        writer.popState();
      });
    }
//    generateDocumentBodyShapeSerializers(context, serializingDocumentShapes);
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
   * <p>Serialization of the http-level components will be inline
   * since there isn't any use for them elsewhere. Serialization
   * of document body components should be delegated, however,
   * as they will need to be re-used in all likelihood.
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
    // TODO: pass topDownIndex into this function
    // TODO: parse topDownIndex for the required imports

    writer.addImport("simple.types.boolean.internaldafny.types", "GetBooleanInput_GetBooleanInput", "DafnyGetBooleanInput");

    writer.write("""
            return DafnyGetBooleanInput(value=input.value)
            """);
  }

  @Override
  public void generateResponseDeserializers(GenerationContext context) {
    var topDownIndex = TopDownIndex.of(context.model());
    var service = context.settings().getService(context.model());
    var deserializingErrorShapes = new TreeSet<ShapeId>();
    var delegator = context.writerDelegator();
    var configSymbol = CodegenUtils.getConfigSymbol(context.settings());
    var transportRequest = context.applicationProtocol().requestType();

    for (OperationShape operation : topDownIndex.getContainedOperations(context.settings().getService())) {
      deserializingErrorShapes.addAll(operation.getErrors(service));

      var deserFunction = getDeserializationFunction(context, operation);
      var output = context.model().expectShape(operation.getOutputShape());
      var outputSymbol = context.symbolProvider().toSymbol(output);
      delegator.useFileWriter(deserFunction.getDefinitionFile(), deserFunction.getNamespace(), writer -> {
        writer.pushState(new RequestSerializerSection(operation));

        writer.write("""
                    async def $L(input: DafnyGetBooleanOutput, config: $T) -> $T:
                        ${C|}
                    """, deserFunction.getName(), configSymbol, outputSymbol,
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
   * <p>Deserialization of the http-level components will be inline
   * since there isn't any use for them elsewhere. Deserialization
   * of document body components should be delegated, however,
   * as they will need to be re-used in all likelihood.
   *
   * <p>This function has the following in scope:
   * <ul>
   *     <li>http_response - the http-level response</li>
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

      // TODO: pass topDownIndex into this function
      // TODO: parse topDownIndex for the required imports
      
      writer.addImport("simple.types.boolean.internaldafny.types", "GetBooleanOutput_GetBooleanOutput", "DafnyGetBooleanOutput");
//      writer.addImport(".config", "Config", "Config");
//      writer.addImport(".models", "GetBooleanOutput", "GetBooleanOutput");

      writer.write("""
            return GetBooleanOutput(value=input.value.value)
      """);
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
    var deserFunction = getErrorDeserializationFunction(context, error);
    var errorSymbol = context.symbolProvider().toSymbol(error);
    var delegator = context.writerDelegator();
    var transportResponse = context.applicationProtocol().responseType();
    var configSymbol = CodegenUtils.getConfigSymbol(context.settings());
    delegator.useFileWriter(deserFunction.getDefinitionFile(), deserFunction.getNamespace(), writer -> {
      writer.pushState(new ErrorDeserializerSection(error));
      writer.addStdlibImport("typing", "Any");
      writer.write("""
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
  private static class HttpMemberSerVisitor extends ShapeVisitor.Default<String> {
    private final GenerationContext context;
    private final PythonWriter writer;
    private final String dataSource;
    private final Location bindingType;
    private final MemberShape member;
    private final Format defaultTimestampFormat;

    /**
     * @param context The generation context.
     * @param writer The writer to add dependencies to.
     * @param bindingType How this value is bound to the operation input.
     * @param dataSource The in-code location of the data to provide an output of
     *                   ({@code input.foo}, {@code entry}, etc.)
     * @param member The member that points to the value being provided.
     * @param defaultTimestampFormat The default timestamp format to use.
     */
    HttpMemberSerVisitor(
        GenerationContext context,
        PythonWriter writer,
        Location bindingType,
        String dataSource,
        MemberShape member,
        Format defaultTimestampFormat
    ) {
      this.context = context;
      this.writer = writer;
      this.dataSource = dataSource;
      this.bindingType = bindingType;
      this.member = member;
      this.defaultTimestampFormat = defaultTimestampFormat;
    }

    @Override
    protected String getDefault(Shape shape) {
      var protocolName = context.protocolGenerator().getName();
      throw new CodegenException(String.format(
          "Unsupported %s binding of %s to %s in %s using the %s protocol",
          bindingType, member.getMemberName(), shape.getType(), member.getContainer(), protocolName));
    }

    @Override
    public String blobShape(BlobShape shape) {
      if (member.getMemberTrait(context.model(), StreamingTrait.class).isPresent()) {
        return dataSource;
      }
      writer.addStdlibImport("base64", "b64encode");
      return format("b64encode(%s).decode('utf-8')", dataSource);
    }

    @Override
    public String booleanShape(BooleanShape shape) {
      return String.format("('true' if %s else 'false')", dataSource);
    }

    @Override
    public String stringShape(StringShape shape) {
      if (bindingType == Location.HEADER) {
        if (shape.hasTrait(MediaTypeTrait.class)) {
          writer.addStdlibImport("base64", "b64encode");
          return format("b64encode(%s.encode('utf-8')).decode('utf-8')", dataSource);
        }
      }
      return dataSource;
    }

    @Override
    public String byteShape(ByteShape shape) {
      // TODO: perform bounds checks
      return integerShape();
    }

    @Override
    public String shortShape(ShortShape shape) {
      // TODO: perform bounds checks
      return integerShape();
    }

    @Override
    public String integerShape(IntegerShape shape) {
      // TODO: perform bounds checks
      return integerShape();
    }

    @Override
    public String longShape(LongShape shape) {
      // TODO: perform bounds checks
      return integerShape();
    }

    @Override
    public String bigIntegerShape(BigIntegerShape shape) {
      return integerShape();
    }

    private String integerShape() {
      return String.format("str(%s)", dataSource);
    }

    @Override
    public String floatShape(FloatShape shape) {
      // TODO: use strict parsing
      return floatShapes();
    }

    @Override
    public String doubleShape(DoubleShape shape) {
      // TODO: use strict parsing
      return floatShapes();
    }

    @Override
    public String bigDecimalShape(BigDecimalShape shape) {
      return floatShapes();
    }

    private String floatShapes() {
      writer.addDependency(SmithyPythonDependency.SMITHY_PYTHON);
      writer.addImport("smithy_python.utils", "serialize_float");
      return String.format("serialize_float(%s)", dataSource);
    }

    @Override
    public String timestampShape(TimestampShape shape) {
      return "timestampshape";
    }
  }

  /**
   * Given context and a source of data, generate an output value provider for the
   * shape. This may use native types (like generating a datetime for timestamps)
   * converters (like a b64decode) or invoke complex type deserializers to
   * manipulate the dataSource into the proper output content.
   */
  private static class HttpMemberDeserVisitor extends ShapeVisitor.Default<String> {

    private final GenerationContext context;
    private final PythonWriter writer;
    private final String dataSource;
    private final Location bindingType;
    private final MemberShape member;
    private final Format defaultTimestampFormat;

    /**
     * @param context The generation context.
     * @param writer The writer to add dependencies to.
     * @param bindingType How this value is bound to the operation output.
     * @param dataSource The in-code location of the data to provide an output of
     *                   ({@code output.foo}, {@code entry}, etc.)
     * @param member The member that points to the value being provided.
     * @param defaultTimestampFormat The default timestamp format to use.
     */
    HttpMemberDeserVisitor(
        GenerationContext context,
        PythonWriter writer,
        Location bindingType,
        String dataSource,
        MemberShape member,
        Format defaultTimestampFormat
    ) {
      this.context = context;
      this.writer = writer;
      this.dataSource = dataSource;
      this.bindingType = bindingType;
      this.member = member;
      this.defaultTimestampFormat = defaultTimestampFormat;
    }

    @Override
    protected String getDefault(Shape shape) {
      var protocolName = context.protocolGenerator().getName();
      throw new CodegenException(String.format(
          "Unsupported %s binding of %s to %s in %s using the %s protocol",
          bindingType, member.getMemberName(), shape.getType(), member.getContainer(), protocolName));
    }

    @Override
    public String blobShape(BlobShape shape) {
      if (bindingType == PAYLOAD) {
        return dataSource;
      }
      throw new CodegenException("Unexpected blob binding location `" + bindingType + "`");
    }

    @Override
    public String booleanShape(BooleanShape shape) {
      switch (bindingType) {
        case QUERY, LABEL, HEADER -> {
          writer.addDependency(SmithyPythonDependency.SMITHY_PYTHON);
          writer.addImport("smithy_python.utils", "strict_parse_bool");
          return "strict_parse_bool(" + dataSource + ")";
        }
        default -> throw new CodegenException("Unexpected boolean binding location `" + bindingType + "`");
      }
    }

    @Override
    public String byteShape(ByteShape shape) {
      // TODO: perform bounds checks
      return integerShape();
    }

    @Override
    public String shortShape(ShortShape shape) {
      // TODO: perform bounds checks
      return integerShape();
    }

    @Override
    public String integerShape(IntegerShape shape) {
      // TODO: perform bounds checks
      return integerShape();
    }

    @Override
    public String longShape(LongShape shape) {
      // TODO: perform bounds checks
      return integerShape();
    }

    @Override
    public String bigIntegerShape(BigIntegerShape shape) {
      return integerShape();
    }

    private String integerShape() {
      return switch (bindingType) {
        case QUERY, LABEL, HEADER, RESPONSE_CODE -> "int(" + dataSource + ")";
        default -> throw new CodegenException("Unexpected integer binding location `" + bindingType + "`");
      };
    }

    @Override
    public String floatShape(FloatShape shape) {
      // TODO: use strict parsing
      return floatShapes();
    }

    @Override
    public String doubleShape(DoubleShape shape) {
      // TODO: use strict parsing
      return floatShapes();
    }

    private String floatShapes() {
      switch (bindingType) {
        case QUERY, LABEL, HEADER -> {
          writer.addDependency(SmithyPythonDependency.SMITHY_PYTHON);
          writer.addImport("smithy_python.utils", "strict_parse_float");
          return "strict_parse_float(" + dataSource + ")";
        }
        default -> throw new CodegenException("Unexpected float binding location `" + bindingType + "`");
      }
    }

    @Override
    public String bigDecimalShape(BigDecimalShape shape) {
      switch (bindingType) {
        case QUERY, LABEL, HEADER -> {
          writer.addStdlibImport("decimal", "Decimal", "_Decimal");
          return "_Decimal(" + dataSource + ")";
        }
        default -> throw new CodegenException("Unexpected bigDecimal binding location `" + bindingType + "`");
      }
    }

    @Override
    public String stringShape(StringShape shape) {
      if ((bindingType == HEADER || bindingType == PREFIX_HEADERS) && shape.hasTrait(MediaTypeTrait.ID)) {
        writer.addStdlibImport("base64", "b64decode");
        return  "b64decode(" + dataSource + ").decode('utf-8')";
      }

      return dataSource;
    }

    @Override
    public String timestampShape(TimestampShape shape) {
      return "timestampshape";
    }

    @Override
    public String listShape(ListShape shape) {
      if (bindingType != HEADER) {
        throw new CodegenException("Unexpected list binding location `" + bindingType + "`");
      }
      var collectionTarget = context.model().expectShape(shape.getMember().getTarget());
      writer.addImport("smithy_python.httputils", "split_header");
      writer.addDependency(SmithyPythonDependency.SMITHY_PYTHON);
      String split = String.format("split_header(%s or '')", dataSource);;

      // Headers that have HTTP_DATE formatted timestamps may not be quoted, so we need
      // to enable special handling for them.
      if (isHttpDate(shape.getMember(), collectionTarget)) {
        split = String.format("split_header(%s or '', True)", dataSource);
      }

      var targetDeserVisitor = new HttpMemberDeserVisitor(
          context, writer, bindingType, "e.strip()", shape.getMember(), defaultTimestampFormat);
      return String.format("[%s for e in %s]", collectionTarget.accept(targetDeserVisitor), split);
    }

    private boolean isHttpDate(MemberShape member, Shape target) {
      if (target.isTimestampShape()) {
        HttpBindingIndex httpIndex = HttpBindingIndex.of(context.model());
        Format format = httpIndex.determineTimestampFormat(member, bindingType, Format.HTTP_DATE);
        return format == Format.HTTP_DATE;
      }
      return false;
    }
  }
}
