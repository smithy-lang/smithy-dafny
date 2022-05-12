// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import org.junit.Test;
import software.amazon.polymorph.util.TestModel;
import software.amazon.polymorph.util.Tokenizer;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;

import java.util.List;
import java.util.function.BiConsumer;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.FROM_DAFNY;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.TO_DAFNY;

public class AwsSdkTypeConversionCodegenTest {
    private static final String SERVICE_NAMESPACE = "com.amazonaws.foobar";
    private static final String SERVICE_NAME = "FoobarService";
    private static final ShapeId SERVICE_SHAPE_ID = ShapeId.fromParts(SERVICE_NAMESPACE, SERVICE_NAME);

    private static AwsSdkTypeConversionCodegen setupCodegen(final BiConsumer<ServiceShape.Builder, ModelAssembler> updater) {
        final Model model = TestModel.setupModel((builder, assembler) -> {
            builder.id(SERVICE_SHAPE_ID);
            updater.accept(builder, assembler);
        });
        return new AwsSdkTypeConversionCodegen(model, SERVICE_SHAPE_ID);
    }

    /**
     * Test that an AWS SDK structure type converter doesn't try to call the member properties' {@code IsSet*} methods,
     * since those are marked internal and are thus inaccessible to our generated code.
     */
    @Test
    public void testGenerateStructureConverterWithOptionalValue() {
        final ShapeId shapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "OptionalInt");
        final ShapeId memberId = shapeId.withMember("int");
        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
                modelAssembler.addUnparsedModel("test.smithy", """
                        namespace %s
                        structure OptionalInt { int: Integer }
                        """.formatted(SERVICE_NAMESPACE)));
        final TypeConversionCodegen.TypeConverter converter = codegen.generateStructureConverter(
                codegen.getModel().expectShape(shapeId, StructureShape.class));
        assertEquals(shapeId, converter.shapeId());

        final List<Tokenizer.ParseToken> actualTokensFromDafny = Tokenizer.tokenize(converter.fromDafny().toString());
        final String structureFromDafnyConverterName = AwsSdkDotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
        final String memberFromDafnyConverterName = AwsSdkDotNetNameResolver.typeConverterForShape(memberId, FROM_DAFNY);
        final List<Tokenizer.ParseToken> expectedTokensFromDafny = Tokenizer.tokenize("""
                public static Amazon.FoobarService.Model.OptionalInt
                        %s(Dafny.Com.Amazonaws.Foobar._IOptionalInt value) {
                    Dafny.Com.Amazonaws.Foobar.OptionalInt concrete = (Dafny.Com.Amazonaws.Foobar.OptionalInt)value;
                    Amazon.FoobarService.Model.OptionalInt converted = new Amazon.FoobarService.Model.OptionalInt();
                    if (concrete.int.is_Some) converted.Int = (int) %s(concrete.int);
                    return converted;
                }
                """.formatted(structureFromDafnyConverterName, memberFromDafnyConverterName));
        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);

        final List<Tokenizer.ParseToken> actualTokensToDafny = Tokenizer.tokenize(converter.toDafny().toString());
        final String structureToDafnyConverterName = AwsSdkDotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
        final String memberToDafnyConverterName = AwsSdkDotNetNameResolver.typeConverterForShape(memberId, TO_DAFNY);
        final List<Tokenizer.ParseToken> expectedTokensToDafny = Tokenizer.tokenize("""
                public static Dafny.Com.Amazonaws.Foobar._IOptionalInt
                        %s(Amazon.FoobarService.Model.OptionalInt value) {
                    int? var_int = value.Int;
                    return new Dafny.Com.Amazonaws.Foobar.OptionalInt(%s(var_int));
                }
                """.formatted(structureToDafnyConverterName, memberToDafnyConverterName));
        assertEquals(expectedTokensToDafny, actualTokensToDafny);
    }

    @Test
    public void testGenerateStructureConverterErrorStructureWithMessage() {
        final ShapeId shapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "OopsException");
        final ShapeId stringShapeId = ShapeId.from("smithy.api#String");
        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
                modelAssembler.addUnparsedModel("test.smithy", """
                        namespace %s
                        @error("client")
                        structure OopsException { message: String }
                        """.formatted(SERVICE_NAMESPACE)));
        final TypeConversionCodegen.TypeConverter converter = codegen.generateStructureConverter(
                codegen.getModel().expectShape(shapeId, StructureShape.class));
        assertEquals(shapeId, converter.shapeId());

        final List<Tokenizer.ParseToken> actualTokensFromDafny = Tokenizer.tokenize(converter.fromDafny().toString());
        final String structureFromDafnyConverterName = AwsSdkDotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
        final String stringFromDafnyConverterName = AwsSdkDotNetNameResolver.typeConverterForShape(stringShapeId, FROM_DAFNY);
        final List<Tokenizer.ParseToken> expectedTokensFromDafny = Tokenizer.tokenize("""
                public static Amazon.FoobarService.Model.OopsException
                        %s(Dafny.Com.Amazonaws.Foobar.OopsException value) {
                    string message = value.message.Count == 0 ? null : %s(value.message);
                    return new Amazon.FoobarService.Model.OopsException(message);
                }""".formatted(
                structureFromDafnyConverterName,
                stringFromDafnyConverterName));
        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);

        final List<Tokenizer.ParseToken> actualTokensToDafny = Tokenizer.tokenize(converter.toDafny().toString());
        final String structureToDafnyConverterName = AwsSdkDotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
        final String stringToDafnyConverterName = AwsSdkDotNetNameResolver.typeConverterForShape(stringShapeId, TO_DAFNY);
        final List<Tokenizer.ParseToken> expectedTokensToDafny = Tokenizer.tokenize("""
                public static Dafny.Com.Amazonaws.Foobar.OopsException
                        %s(Amazon.FoobarService.Model.OopsException value) {
                    Dafny.ISequence<char> message = System.String.IsNullOrEmpty(value.Message)
                        ? Dafny.Sequence<char>.Empty
                        : %s(value.Message);
                    return new Dafny.Com.Amazonaws.Foobar.OopsException { message = message };
                }""".formatted(
                structureToDafnyConverterName,
                stringToDafnyConverterName));
        assertEquals(expectedTokensToDafny, actualTokensToDafny);
    }
}
