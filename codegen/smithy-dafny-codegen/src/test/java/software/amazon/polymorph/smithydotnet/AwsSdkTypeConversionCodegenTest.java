// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

import java.util.function.BiConsumer;
import software.amazon.polymorph.util.TestModel;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;

public class AwsSdkTypeConversionCodegenTest {

  // TODO: Apply "Errors" refactor to Tests
  // https://github.com/smithy-lang/smithy-dafny/issues/25
  private static final String SERVICE_NAMESPACE = "com.amazonaws.foobar";
  private static final String SERVICE_NAME = "FoobarService";
  private static final ShapeId SERVICE_SHAPE_ID = ShapeId.fromParts(
    SERVICE_NAMESPACE,
    SERVICE_NAME
  );

  private static AwsSdkTypeConversionCodegen setupCodegen(
    final BiConsumer<ServiceShape.Builder, ModelAssembler> updater
  ) {
    final Model model = TestModel.setupModel((builder, assembler) -> {
      builder.id(SERVICE_SHAPE_ID);
      updater.accept(builder, assembler);
    });
    final ServiceShape serviceShape = model.expectShape(
      SERVICE_SHAPE_ID,
      ServiceShape.class
    );
    return new AwsSdkTypeConversionCodegen(model, serviceShape);
  }
  // Removed 2023-01-27 for output-local-service-test
  //    /**
  //     * Test that an AWS SDK structure type converter doesn't try to call the member properties' {@code IsSet*} methods,
  //     * since those are marked internal and are thus inaccessible to our generated code.
  //     */
  //    @Test
  //    public void testGenerateStructureConverterWithOptionalValue() {
  //        final ShapeId shapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "OptionalInt");
  //        final ShapeId memberId = shapeId.withMember("int");
  //        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
  //                modelAssembler.addUnparsedModel("test.smithy", """
  //                        namespace %s
  //                        structure OptionalInt { int: Integer }
  //                        """.formatted(SERVICE_NAMESPACE)));
  //        final TypeConversionCodegen.TypeConverter converter = codegen.generateStructureConverter(
  //                codegen.getModel().expectShape(shapeId, StructureShape.class));
  //        assertEquals(shapeId, converter.shapeId());
  //
  //        final List<Tokenizer.ParseToken> actualTokensFromDafny = Tokenizer.tokenize(converter.fromDafny().toString());
  //        final String structureFromDafnyConverterName = AwsSdkDotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
  //        final String memberFromDafnyConverterName = AwsSdkDotNetNameResolver.typeConverterForShape(memberId, FROM_DAFNY);
  //        final List<Tokenizer.ParseToken> expectedTokensFromDafny = Tokenizer.tokenize("""
  //                public static Amazon.FoobarService.Model.OptionalInt
  //                        %s(Dafny.Com.Amazonaws.Foobar.Types._IOptionalInt value) {
  //                    Dafny.Com.Amazonaws.Foobar.Types.OptionalInt concrete = (Dafny.Com.Amazonaws.Foobar.Types.OptionalInt)value;
  //                    Amazon.FoobarService.Model.OptionalInt converted = new Amazon.FoobarService.Model.OptionalInt();
  //                    if (concrete._int.is_Some) converted.Int = (int) %s(concrete._int);
  //                    return converted;
  //                }
  //                """.formatted(structureFromDafnyConverterName, memberFromDafnyConverterName));
  //        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);
  //
  //        final List<Tokenizer.ParseToken> actualTokensToDafny = Tokenizer.tokenize(converter.toDafny().toString());
  //        final String structureToDafnyConverterName = AwsSdkDotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
  //        final String memberToDafnyConverterName = AwsSdkDotNetNameResolver.typeConverterForShape(memberId, TO_DAFNY);
  //        final List<Tokenizer.ParseToken> expectedTokensToDafny = Tokenizer.tokenize("""
  //                public static Dafny.Com.Amazonaws.Foobar.Types._IOptionalInt
  //                        %s(Amazon.FoobarService.Model.OptionalInt value) {
  //                    int? var_int = value.Int;
  //                    return new Dafny.Com.Amazonaws.Foobar.Types.OptionalInt(%s(var_int));
  //                }
  //                """.formatted(structureToDafnyConverterName, memberToDafnyConverterName));
  //        assertEquals(expectedTokensToDafny, actualTokensToDafny);
  //    }

  //    @Test
  //    public void testGenerateStructureConverterErrorStructureWithMessage() {
  //        final ShapeId shapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "OopsException");
  //        final ShapeId stringShapeId = ShapeId.from("smithy.api#String");
  //        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
  //                modelAssembler.addUnparsedModel("test.smithy", """
  //                        namespace %s
  //                        @error("client")
  //                        structure OopsException { message: String }
  //                        """.formatted(SERVICE_NAMESPACE)));
  //        final TypeConversionCodegen.TypeConverter converter = codegen.generateStructureConverter(
  //                codegen.getModel().expectShape(shapeId, StructureShape.class));
  //        assertEquals(shapeId, converter.shapeId());
  //
  //        final List<Tokenizer.ParseToken> actualTokensFromDafny = Tokenizer.tokenize(converter.fromDafny().toString());
  //        final String structureFromDafnyConverterName = AwsSdkDotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
  //        final String stringFromDafnyConverterName = AwsSdkDotNetNameResolver.typeConverterForShape(stringShapeId, FROM_DAFNY);
  //        final List<Tokenizer.ParseToken> expectedTokensFromDafny = Tokenizer.tokenize("""
  //                public static Amazon.FoobarService.Model.OopsException
  //                        %s(Dafny.Com.Amazonaws.Foobar.Types.Error_OopsException value) {
  //                    return new Amazon.FoobarService.Model.OopsException(
  //                        FromDafny_N3_com__N9_amazonaws__N6_foobar__S13_OopsException__M7_message(value._message)
  //                    );
  //                }""".formatted(
  //                structureFromDafnyConverterName,
  //                stringFromDafnyConverterName));
  //        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);
  //
  //        final List<Tokenizer.ParseToken> actualTokensToDafny = Tokenizer.tokenize(converter.toDafny().toString());
  //        final String structureToDafnyConverterName = AwsSdkDotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
  //        final String stringToDafnyConverterName = AwsSdkDotNetNameResolver.typeConverterForShape(stringShapeId, TO_DAFNY);
  //        final List<Tokenizer.ParseToken> expectedTokensToDafny = Tokenizer.tokenize("""
  //                public static Dafny.Com.Amazonaws.Foobar.Types.Error_OopsException
  //                        %s(Amazon.FoobarService.Model.OopsException value) {
  //                    string var_message = value.Message;
  //                    return new Dafny.Com.Amazonaws.Foobar.Types.Error_OopsException(
  //                        ToDafny_N3_com__N9_amazonaws__N6_foobar__S13_OopsException__M7_message(var_message)
  //                    );
  //                }""".formatted(
  //                structureToDafnyConverterName,
  //                stringToDafnyConverterName));
  //        assertEquals(expectedTokensToDafny, actualTokensToDafny);
  //    }
}
