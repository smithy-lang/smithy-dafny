// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import org.junit.Test;
import software.amazon.polymorph.smithydotnet.TypeConversionCodegen.TypeConverter;
import software.amazon.polymorph.traits.ClientConfigTrait;
import software.amazon.polymorph.smithydotnet.util.CSharpLexer;
import software.amazon.polymorph.smithydotnet.util.TestModel;
import software.amazon.polymorph.smithydotnet.util.Tokenizer;
import software.amazon.polymorph.smithydotnet.util.Tokenizer.ParseToken;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.shapes.BlobShape;
import software.amazon.smithy.model.shapes.BooleanShape;
import software.amazon.smithy.model.shapes.IntegerShape;
import software.amazon.smithy.model.shapes.ListShape;
import software.amazon.smithy.model.shapes.LongShape;
import software.amazon.smithy.model.shapes.MapShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.TimestampShape;

import java.nio.file.Path;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.junit.Assert.*;
import static software.amazon.polymorph.smithydotnet.TypeConversionCodegen.TYPE_CONVERSION_CLASS_PATH;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.FROM_DAFNY;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.TO_DAFNY;
import static software.amazon.polymorph.smithydotnet.util.TestModel.SERVICE_NAMESPACE;
import static software.amazon.polymorph.smithydotnet.util.TestModel.SERVICE_SHAPE_ID;

public class TypeConversionCodegenTest {
    private static TypeConversionCodegen setupCodegen(final BiConsumer<ServiceShape.Builder, ModelAssembler> updater) {
        final Model model = TestModel.setupModel(updater);
        return new TypeConversionCodegen(model, SERVICE_SHAPE_ID);
    }

    private static List<ParseToken> generateAndTokenize(final TypeConversionCodegen codegen) {
        final Map<Path, TokenTree> generatedCode = codegen.generate();
        assertTrue(generatedCode.containsKey(TYPE_CONVERSION_CLASS_PATH));
        final String actualCode = Objects.requireNonNull(generatedCode.get(TYPE_CONVERSION_CLASS_PATH)).toString();
        return Tokenizer.tokenize(actualCode);
    }

    @Test
    public void testGenerateEmptyModel() {
        final TypeConversionCodegen codegen = setupCodegen((_builder, _modelAssembler) -> {});
        final List<ParseToken> actualTokens = generateAndTokenize(codegen);
        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                using System.Linq;
                using Aws.Crypto;
                namespace Test.Foobar {
                    internal static class TypeConversion {}
                }
                """);
        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateSimpleModel() {
        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) -> {
            builder.addOperation(ShapeId.fromParts(SERVICE_NAMESPACE, "DoBar"));
            modelAssembler.addUnparsedModel("test.smithy", """
                        namespace %s
                        operation DoBar { input: DoBarInput, output: DoBarOutput }
                        structure DoBarInput { bool: Boolean }
                        structure DoBarOutput { int: Integer }
                        """.formatted(SERVICE_NAMESPACE));
        });
        final Set<ParseToken> actualTokens = new HashSet<>(generateAndTokenize(codegen));

        final Stream<ParseToken> expectedConverterMethods = Stream.of(
                SERVICE_NAMESPACE + "#DoBarInput",
                SERVICE_NAMESPACE + "#DoBarInput$bool",
                SERVICE_NAMESPACE + "#DoBarOutput",
                SERVICE_NAMESPACE + "#DoBarOutput$int",
                "smithy.api#Boolean",
                "smithy.api#Integer"
                )
                .map(ShapeId::from)
                .flatMap(shapeId -> Stream.of(
                        DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY),
                        DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY)
                ))
                .map(converterName -> new ParseToken(converterName, CSharpLexer.IDENTIFIER));
        assertTrue(expectedConverterMethods.allMatch(actualTokens::contains));
    }

    @Test
    public void testFindShapeIdsToConvert() {
        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) -> {
            builder.addOperation(ShapeId.fromParts(SERVICE_NAMESPACE, "DoBar"));
            builder.addTrait(ClientConfigTrait.builder()
                    .clientConfigId(ShapeId.fromParts(SERVICE_NAMESPACE, "FoobarConfig"))
                    .build());
            modelAssembler.addUnparsedModel("test.smithy", """
                        namespace %s
                        structure FoobarConfig {}
                        resource FooResource { operations: [DoBaz] }
                        operation DoBar { input: DoBarInput }
                        operation DoBaz { output: DoBazOutput }
                        structure DoBarInput { qux: Qux }
                        structure DoBazOutput { xyzzy: Xyzzy }
                        map Qux { key: String, value: Integer }
                        list Xyzzy { member: Blob }
                        """.formatted(SERVICE_NAMESPACE));
        });
        final Set<ShapeId> expectedShapeIds = Stream.of(
                SERVICE_NAMESPACE + "#FoobarConfig",
                SERVICE_NAMESPACE + "#DoBarInput",
                SERVICE_NAMESPACE + "#DoBarInput$qux",
                SERVICE_NAMESPACE + "#DoBazOutput",
                SERVICE_NAMESPACE + "#DoBazOutput$xyzzy",
                SERVICE_NAMESPACE + "#Qux",
                SERVICE_NAMESPACE + "#Qux$key",
                SERVICE_NAMESPACE + "#Qux$value",
                SERVICE_NAMESPACE + "#Xyzzy",
                SERVICE_NAMESPACE + "#Xyzzy$member",
                "smithy.api#String",
                "smithy.api#Integer",
                "smithy.api#Blob"
        ).map(ShapeId::from).collect(Collectors.toSet());

        final Set<ShapeId> actualShapeIds = codegen.findShapeIdsToConvert();
        assertEquals(expectedShapeIds, actualShapeIds);
    }

    @Test
    public void testGenerateBlobConverter() {
        final ShapeId shapeId = ShapeId.from("smithy.api#Blob");
        final TypeConversionCodegen codegen = setupCodegen((_builder, _modelAssembler) -> {});
        final TypeConverter converter = codegen.generateBlobConverter(BlobShape.builder().id(shapeId).build());
        assertEquals(shapeId, converter.shapeId());

        final List<ParseToken> actualTokensFromDafny = Tokenizer.tokenize(converter.fromDafny().toString());
        final String fromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
        final List<ParseToken> expectedTokensFromDafny = Tokenizer.tokenize("""
                public static System.IO.MemoryStream %s(Dafny.ISequence<byte> value) {
                    return new System.IO.MemoryStream(value.Elements);
                }
                """.formatted(fromDafnyConverterName));
        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);

        final List<ParseToken> actualTokensToDafny = Tokenizer.tokenize(converter.toDafny().toString());
        final String toDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
        final List<ParseToken> expectedTokensToDafny = Tokenizer.tokenize("""
                public static Dafny.ISequence<byte> %s(System.IO.MemoryStream value) {
                    return Dafny.Sequence<byte>.FromArray(value.ToArray());
                }
                """.formatted(toDafnyConverterName));
        assertEquals(expectedTokensToDafny, actualTokensToDafny);
    }

    @Test
    public void testGenerateBooleanConverter() {
        final ShapeId shapeId = ShapeId.from("smithy.api#Boolean");
        final TypeConversionCodegen codegen = setupCodegen((_builder, _modelAssembler) -> {});
        final TypeConverter converter = codegen.generateBooleanConverter(BooleanShape.builder().id(shapeId).build());
        assertEquals(shapeId, converter.shapeId());

        final List<ParseToken> actualTokensFromDafny = Tokenizer.tokenize(converter.fromDafny().toString());
        final String fromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
        final List<ParseToken> expectedTokensFromDafny = Tokenizer.tokenize(
                "public static bool %s(bool value) { return value; }".formatted(fromDafnyConverterName));
        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);

        final List<ParseToken> actualTokensToDafny = Tokenizer.tokenize(converter.toDafny().toString());
        final String toDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
        final List<ParseToken> expectedTokensToDafny = Tokenizer.tokenize(
                "public static bool %s(bool value) { return value; }".formatted(toDafnyConverterName));
        assertEquals(expectedTokensToDafny, actualTokensToDafny);
    }

    @Test
    public void testGenerateStringConverterRegularString() {
        final ShapeId shapeId = ShapeId.from("smithy.api#String");
        final TypeConversionCodegen codegen = setupCodegen((_builder, _modelAssembler) -> {});
        final TypeConverter converter = codegen.generateStringConverter(StringShape.builder().id(shapeId).build());
        assertEquals(shapeId, converter.shapeId());

        final List<ParseToken> actualTokensFromDafny = Tokenizer.tokenize(converter.fromDafny().toString());
        final String fromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
        final List<ParseToken> expectedTokensFromDafny = Tokenizer.tokenize("""
                public static string %s(Dafny.ISequence<char> value) {
                    return new string(value.Elements);
                }""".formatted(fromDafnyConverterName));
        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);

        final List<ParseToken> actualTokensToDafny = Tokenizer.tokenize(converter.toDafny().toString());
        final String toDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
        final List<ParseToken> expectedTokensToDafny = Tokenizer.tokenize("""
                public static Dafny.ISequence<char> %s(string value) {
                    return Dafny.Sequence<char>.FromString(value);
                }""".formatted(toDafnyConverterName));
        assertEquals(expectedTokensToDafny, actualTokensToDafny);
    }

    @Test
    public void testGenerateStringConverterEnumString() {
        final ShapeId shapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "AnEnum");
        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
                modelAssembler.addUnparsedModel("test.smithy", """
                        namespace %s
                        @enum([
                            { name: "VERSION_A", value: "bar" },
                            { name: "VERSION_B", value: "baz" },
                        ])
                        string AnEnum
                        """.formatted(SERVICE_NAMESPACE)));
        final TypeConverter converter = codegen.generateStringConverter(
                codegen.getModel().expectShape(shapeId, StringShape.class));
        assertEquals(shapeId, converter.shapeId());

        final List<ParseToken> actualTokensFromDafny = Tokenizer.tokenize(converter.fromDafny().toString());
        final String fromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
        final List<ParseToken> expectedTokensFromDafny = Tokenizer.tokenize("""
                public static Test.Foobar.AnEnum %s(Dafny.Test.Foobar.AnEnum value) {
                    if (value.is_VERSION__A) return Test.Foobar.AnEnum.VERSION_A;
                    if (value.is_VERSION__B) return Test.Foobar.AnEnum.VERSION_B;
                    throw new System.ArgumentException("Invalid Test.Foobar.AnEnum value");
                }""".formatted(fromDafnyConverterName));
        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);

        final List<ParseToken> actualTokensToDafny = Tokenizer.tokenize(converter.toDafny().toString());
        final String toDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
        final List<ParseToken> expectedTokensToDafny = Tokenizer.tokenize("""
                public static Dafny.Test.Foobar.AnEnum %s(Test.Foobar.AnEnum value) {
                    if (Test.Foobar.AnEnum.VERSION_A.Equals(value)) return Dafny.Test.Foobar.AnEnum.create_VERSION__A();
                    if (Test.Foobar.AnEnum.VERSION_B.Equals(value)) return Dafny.Test.Foobar.AnEnum.create_VERSION__B();
                    throw new System.ArgumentException("Invalid Test.Foobar.AnEnum value");
                }""".formatted(toDafnyConverterName));
        assertEquals(expectedTokensToDafny, actualTokensToDafny);
    }

    /**
     * Test that we generate an enum converter correctly when the enum has only one constructor.
     *
     * This is different than the "normal" case because Dafny doesn't generate a compiled constructor when there's only
     * one.
     */
    @Test
    public void testGenerateStringConverterEnumStringSingleConstructor() {
        final ShapeId shapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "AnEnum");
        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
                modelAssembler.addUnparsedModel("test.smithy", """
                        namespace %s
                        @enum([{ name: "VERSION_A", value: "bar" }])
                        string AnEnum
                        """.formatted(SERVICE_NAMESPACE)));
        final TypeConverter converter = codegen.generateStringConverter(
                codegen.getModel().expectShape(shapeId, StringShape.class));
        assertEquals(shapeId, converter.shapeId());

        final List<ParseToken> actualTokensFromDafny = Tokenizer.tokenize(converter.fromDafny().toString());
        final String fromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
        final List<ParseToken> expectedTokensFromDafny = Tokenizer.tokenize("""
                public static Test.Foobar.AnEnum %s(Dafny.Test.Foobar.AnEnum value) {
                    if (value.is_VERSION__A) return Test.Foobar.AnEnum.VERSION_A;
                    throw new System.ArgumentException("Invalid Test.Foobar.AnEnum value");
                }""".formatted(fromDafnyConverterName));
        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);

        final List<ParseToken> actualTokensToDafny = Tokenizer.tokenize(converter.toDafny().toString());
        final String toDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
        final List<ParseToken> expectedTokensToDafny = Tokenizer.tokenize("""
                public static Dafny.Test.Foobar.AnEnum %s(Test.Foobar.AnEnum value) {
                    if (Test.Foobar.AnEnum.VERSION_A.Equals(value)) return new Dafny.Test.Foobar.AnEnum();
                    throw new System.ArgumentException("Invalid Test.Foobar.AnEnum value");
                }""".formatted(toDafnyConverterName));
        assertEquals(expectedTokensToDafny, actualTokensToDafny);
    }

    @Test
    public void testGenerateStringConverterUtf8Bytes() {
        final ShapeId shapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Utf8BytesString");
        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
                modelAssembler.addUnparsedModel("test.smithy", """
                        namespace %s
                        use aws.polymorph#dafnyUtf8Bytes
                        @dafnyUtf8Bytes
                        string Utf8BytesString
                        """.formatted(SERVICE_NAMESPACE)));
        final TypeConverter converter = codegen.generateStringConverter(
                codegen.getModel().expectShape(shapeId, StringShape.class));
        assertEquals(shapeId, converter.shapeId());

        final List<ParseToken> actualTokensFromDafny = Tokenizer.tokenize(converter.fromDafny().toString());
        final String fromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
        final List<ParseToken> expectedTokensFromDafny = Tokenizer.tokenize("""
                public static string %s(Dafny.ISequence<byte> value) {
                    System.Text.UTF8Encoding utf8 = new System.Text.UTF8Encoding(false, true);
                    return utf8.GetString(value.Elements);
                }""".formatted(fromDafnyConverterName));
        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);

        final List<ParseToken> actualTokensToDafny = Tokenizer.tokenize(converter.toDafny().toString());
        final String toDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
        final List<ParseToken> expectedTokensToDafny = Tokenizer.tokenize("""
                public static Dafny.ISequence<byte> %s(string value) {
                    System.Text.UTF8Encoding utf8 = new System.Text.UTF8Encoding(false, true);
                    return Dafny.Sequence<byte>.FromArray(utf8.GetBytes(value));
                }""".formatted(toDafnyConverterName));
        assertEquals(expectedTokensToDafny, actualTokensToDafny);
    }

    @Test
    public void testGenerateIntegerConverter() {
        final ShapeId shapeId = ShapeId.from("smithy.api#Integer");
        final TypeConversionCodegen codegen = setupCodegen((_builder, _modelAssembler) -> {});
        final TypeConverter converter = codegen.generateIntegerConverter(IntegerShape.builder().id(shapeId).build());
        assertEquals(shapeId, converter.shapeId());

        final List<ParseToken> actualTokensFromDafny = Tokenizer.tokenize(converter.fromDafny().toString());
        final String fromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
        final List<ParseToken> expectedTokensFromDafny = Tokenizer.tokenize(
                "public static int %s(int value) { return value; }".formatted(fromDafnyConverterName));
        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);

        final List<ParseToken> actualTokensToDafny = Tokenizer.tokenize(converter.toDafny().toString());
        final String toDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
        final List<ParseToken> expectedTokensToDafny = Tokenizer.tokenize(
                "public static int %s(int value) { return value; }".formatted(toDafnyConverterName));
        assertEquals(expectedTokensToDafny, actualTokensToDafny);
    }

    @Test
    public void testGenerateLongConverter() {
        final ShapeId shapeId = ShapeId.from("smithy.api#Long");
        final TypeConversionCodegen codegen = setupCodegen((_builder, _modelAssembler) -> {});
        final TypeConverter converter = codegen.generateLongConverter(LongShape.builder().id(shapeId).build());
        assertEquals(shapeId, converter.shapeId());

        final List<ParseToken> actualTokensFromDafny = Tokenizer.tokenize(converter.fromDafny().toString());
        final String fromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
        final List<ParseToken> expectedTokensFromDafny = Tokenizer.tokenize(
                "public static long %s(long value) { return value; }".formatted(fromDafnyConverterName));
        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);

        final List<ParseToken> actualTokensToDafny = Tokenizer.tokenize(converter.toDafny().toString());
        final String toDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
        final List<ParseToken> expectedTokensToDafny = Tokenizer.tokenize(
                "public static long %s(long value) { return value; }".formatted(toDafnyConverterName));
        assertEquals(expectedTokensToDafny, actualTokensToDafny);
    }

    @Test
    public void testGenerateTimestampConverter() {
        final ShapeId shapeId = ShapeId.from("smithy.api#Timestamp");
        final TypeConversionCodegen codegen = setupCodegen((_builder, _modelAssembler) -> {});
        final TypeConverter converter = codegen.generateTimestampConverter(
                TimestampShape.builder().id(shapeId).build());
        assertEquals(shapeId, converter.shapeId());

        final List<ParseToken> actualTokensFromDafny = Tokenizer.tokenize(converter.fromDafny().toString());
        final String fromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
        final List<ParseToken> expectedTokensFromDafny = Tokenizer.tokenize("""
                public static System.DateTime %s(Dafny.ISequence<char> value) {
                    System.Globalization.CultureInfo culture = new System.Globalization.CultureInfo("");
                    string timestampString = new string(value.Elements);
                    return System.DateTime.ParseExact(timestampString, "s", culture);
                }
                """.formatted(fromDafnyConverterName));
        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);

        final List<ParseToken> actualTokensToDafny = Tokenizer.tokenize(converter.toDafny().toString());
        final String toDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
        final List<ParseToken> expectedTokensToDafny = Tokenizer.tokenize("""
                public static Dafny.ISequence<char> %s(System.DateTime value) {
                    System.Globalization.CultureInfo culture = new System.Globalization.CultureInfo("");
                    string timestampString = value.ToString("s", culture);
                    return Dafny.Sequence<char>.FromString(timestampString);
                }
                """.formatted(toDafnyConverterName));
        assertEquals(expectedTokensToDafny, actualTokensToDafny);
    }

    @Test
    public void testGenerateListConverter() {
        final ShapeId shapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "IntList");
        final ShapeId memberShapeId = shapeId.withMember("member");
        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
                modelAssembler.addUnparsedModel("test.smithy", """
                        namespace %s
                        list IntList {
                            member: Integer
                        }
                        """.formatted(SERVICE_NAMESPACE)));
        final TypeConverter converter = codegen.generateListConverter(
                codegen.getModel().expectShape(shapeId, ListShape.class));
        assertEquals(shapeId, converter.shapeId());

        final List<ParseToken> actualTokensFromDafny = Tokenizer.tokenize(converter.fromDafny().toString());
        final String listFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
        final String intFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(memberShapeId, FROM_DAFNY);
        final List<ParseToken> expectedTokensFromDafny = Tokenizer.tokenize("""
                public static System.Collections.Generic.List<int> %s(Dafny.ISequence<int> value) {
                    return new System.Collections.Generic.List<int>(value.Elements.Select(%s));
                }""".formatted(listFromDafnyConverterName, intFromDafnyConverterName));
        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);

        final List<ParseToken> actualTokensToDafny = Tokenizer.tokenize(converter.toDafny().toString());
        final String listToDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
        final String intToDafnyConverterName = DotNetNameResolver.typeConverterForShape(memberShapeId, TO_DAFNY);
        final List<ParseToken> expectedTokensToDafny = Tokenizer.tokenize("""
                public static Dafny.ISequence<int> %s(System.Collections.Generic.List<int> value) {
                    return Dafny.Sequence<int>.FromArray(value.Select(%s).ToArray());
                }""".formatted(listToDafnyConverterName, intToDafnyConverterName));
        assertEquals(expectedTokensToDafny, actualTokensToDafny);
    }

    @Test
    public void testGenerateMapConverter() {
        final ShapeId shapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "BoolMap");
        final ShapeId keyMemberId = shapeId.withMember("key");
        final ShapeId valueMemberId = shapeId.withMember("value");
        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
                modelAssembler.addUnparsedModel("test.smithy", """
                        namespace %s
                        map BoolMap {
                            key: String,
                            value: Boolean,
                        }
                        """.formatted(SERVICE_NAMESPACE)));
        final TypeConverter converter = codegen.generateMapConverter(
                codegen.getModel().expectShape(shapeId, MapShape.class));
        assertEquals(shapeId, converter.shapeId());

        final List<ParseToken> actualTokensFromDafny = Tokenizer.tokenize(converter.fromDafny().toString());
        final String mapFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
        final String keyFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(keyMemberId, FROM_DAFNY);
        final String valueFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(valueMemberId, FROM_DAFNY);
        final List<ParseToken> expectedTokensFromDafny = Tokenizer.tokenize("""
                public static System.Collections.Generic.Dictionary<string, bool> %s(
                        Dafny.IMap<Dafny.ISequence<char>, bool> value) {
                    return value.ItemEnumerable.ToDictionary(pair => %s(pair.Car), pair => %s(pair.Cdr));
                }""".formatted(mapFromDafnyConverterName, keyFromDafnyConverterName, valueFromDafnyConverterName));
        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);

        final List<ParseToken> actualTokensToDafny = Tokenizer.tokenize(converter.toDafny().toString());
        final String mapToDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
        final String keyToDafnyConverterName = DotNetNameResolver.typeConverterForShape(keyMemberId, TO_DAFNY);
        final String valueToDafnyConverterName = DotNetNameResolver.typeConverterForShape(valueMemberId, TO_DAFNY);
        final List<ParseToken> expectedTokensToDafny = Tokenizer.tokenize("""
                public static Dafny.IMap<Dafny.ISequence<char>, bool> %s(
                        System.Collections.Generic.Dictionary<string, bool> value) {
                    return Dafny.Map<Dafny.ISequence<char>, bool>.FromCollection(
                        value.Select(pair =>
                            new Dafny.Pair<Dafny.ISequence<char>, bool>(%s(pair.Key), %s(pair.Value))
                        )
                    );
                }""".formatted(mapToDafnyConverterName, keyToDafnyConverterName, valueToDafnyConverterName));
        assertEquals(expectedTokensToDafny, actualTokensToDafny);
    }

    @Test
    public void testGenerateStructureConverterRegularStructure() {
        final ShapeId shapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "IntAndBool");
        final ShapeId intMemberId = shapeId.withMember("someInt");
        final ShapeId boolMemberId = shapeId.withMember("someBool");
        final ShapeId stringMemberId = shapeId.withMember("someString");
        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
                modelAssembler.addUnparsedModel("test.smithy", """
                        namespace %s
                        structure IntAndBool {
                            someInt: Integer,
                            @required
                            someBool: Boolean,
                            someString: String,
                        }
                        """.formatted(SERVICE_NAMESPACE)));
        final TypeConverter converter = codegen.generateStructureConverter(
                codegen.getModel().expectShape(shapeId, StructureShape.class));
        assertEquals(shapeId, converter.shapeId());

        final List<ParseToken> actualTokensFromDafny = Tokenizer.tokenize(converter.fromDafny().toString());
        final String structureFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
        final String intFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(intMemberId, FROM_DAFNY);
        final String boolFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(boolMemberId, FROM_DAFNY);
        final String stringFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(stringMemberId, FROM_DAFNY);
        final List<ParseToken> expectedTokensFromDafny = Tokenizer.tokenize("""
                public static Test.Foobar.IntAndBool %s(Dafny.Test.Foobar.IntAndBool value) {
                    Test.Foobar.IntAndBool converted = new Test.Foobar.IntAndBool();
                    if (value.someInt.is_Some) converted.SomeInt = (int) %s(value.someInt);
                    converted.SomeBool = (bool) %s(value.someBool);
                    if (value.someString.is_Some) converted.SomeString = (string) %s(value.someString);
                    return converted;
                }""".formatted(
                        structureFromDafnyConverterName,
                        intFromDafnyConverterName,
                        boolFromDafnyConverterName,
                        stringFromDafnyConverterName));
        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);

        final List<ParseToken> actualTokensToDafny = Tokenizer.tokenize(converter.toDafny().toString());
        final String structureToDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
        final String intToDafnyConverterName = DotNetNameResolver.typeConverterForShape(intMemberId, TO_DAFNY);
        final String boolToDafnyConverterName = DotNetNameResolver.typeConverterForShape(boolMemberId, TO_DAFNY);
        final String stringToDafnyConverterName = DotNetNameResolver.typeConverterForShape(stringMemberId, TO_DAFNY);
        final List<ParseToken> expectedTokensToDafny = Tokenizer.tokenize("""
                public static Dafny.Test.Foobar.IntAndBool %s(Test.Foobar.IntAndBool value) {
                    return new Dafny.Test.Foobar.IntAndBool(
                        %s(value.SomeInt),
                        %s(value.SomeBool),
                        %s(value.SomeString)
                    );
                }""".formatted(
                        structureToDafnyConverterName,
                        intToDafnyConverterName,
                        boolToDafnyConverterName,
                        stringToDafnyConverterName));
        assertEquals(expectedTokensToDafny, actualTokensToDafny);
    }

    @Test
    public void testGenerateStructureConverterReferenceStructure() {
        final ShapeId shapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "ThingReference");
        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
                modelAssembler.addUnparsedModel("test.smithy", """
                        namespace %s
                        use aws.polymorph#reference
                        resource Thing {}
                        @reference(resource: Thing)
                        structure ThingReference {}
                        """.formatted(SERVICE_NAMESPACE)));
        final TypeConverter converter = codegen.generateStructureConverter(
                codegen.getModel().expectShape(shapeId, StructureShape.class));
        assertEquals(shapeId, converter.shapeId());

        final List<ParseToken> actualTokensFromDafny = Tokenizer.tokenize(converter.fromDafny().toString());
        final String structureFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
        final List<ParseToken> expectedTokensFromDafny = Tokenizer.tokenize("""
                public static Test.Foobar.IThing %s(Dafny.Test.Foobar.IThing value) {
                    return new Thing(value);
                }""".formatted(structureFromDafnyConverterName));
        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);

        final List<ParseToken> actualTokensToDafny = Tokenizer.tokenize(converter.toDafny().toString());
        final String structureToDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
        final List<ParseToken> expectedTokensToDafny = Tokenizer.tokenize("""
                public static Dafny.Test.Foobar.IThing %s(Test.Foobar.IThing value) {
                    if (value is Thing valueWithImpl) {
                        return valueWithImpl._impl;
                    }
                    throw new System.ArgumentException(
                        "Custom implementations of Test.Foobar.IThing are not supported yet");
                }""".formatted(structureToDafnyConverterName));
        assertEquals(expectedTokensToDafny, actualTokensToDafny);
    }

    @Test
    public void testGenerateStructureConverterPositionalStructure() {
        final ShapeId shapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "CreateThingOutput");
        final ShapeId memberShapeId = shapeId.withMember("thing");
        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
                modelAssembler.addUnparsedModel("test.smithy", """
                        namespace %s
                        use aws.polymorph#positional
                        use aws.polymorph#reference
                        resource Thing {}
                        @reference(resource: Thing)
                        structure ThingReference {}
                        @positional
                        structure CreateThingOutput { thing: ThingReference }
                        """.formatted(SERVICE_NAMESPACE)));
        final TypeConverter converter = codegen.generateStructureConverter(
                codegen.getModel().expectShape(shapeId, StructureShape.class));
        assertEquals(shapeId, converter.shapeId());

        final List<ParseToken> actualTokensFromDafny = Tokenizer.tokenize(converter.fromDafny().toString());
        final String structureFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
        final String memberFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(memberShapeId, FROM_DAFNY);
        final List<ParseToken> expectedTokensFromDafny = Tokenizer.tokenize("""
                public static Test.Foobar.IThing %s(Dafny.Test.Foobar.IThing value) {
                    return %s(value);
                }""".formatted(structureFromDafnyConverterName, memberFromDafnyConverterName));
        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);

        final List<ParseToken> actualTokensToDafny = Tokenizer.tokenize(converter.toDafny().toString());
        final String structureToDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
        final String memberToDafnyConverterName = DotNetNameResolver.typeConverterForShape(memberShapeId, TO_DAFNY);
        final List<ParseToken> expectedTokensToDafny = Tokenizer.tokenize("""
                public static Dafny.Test.Foobar.IThing %s(Test.Foobar.IThing value) {
                    return %s(value);
                }""".formatted(structureToDafnyConverterName, memberToDafnyConverterName));
        assertEquals(expectedTokensToDafny, actualTokensToDafny);
    }

    @Test
    public void testGenerateMemberConverterRequired() {
        final ShapeId containerShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Container");
        final ShapeId memberShapeId = containerShapeId.withMember("content");
        final ShapeId targetShapeId = ShapeId.from("smithy.api#Integer");
        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
                modelAssembler.addUnparsedModel("test.smithy", """
                        namespace %s
                        structure Container {
                            @required
                            content: Integer
                        }
                        """.formatted(SERVICE_NAMESPACE)));
        final TypeConverter converter = codegen.generateMemberConverter(
                codegen.getModel().expectShape(memberShapeId, MemberShape.class));
        assertEquals(memberShapeId, converter.shapeId());

        final List<ParseToken> actualTokensFromDafny = Tokenizer.tokenize(converter.fromDafny().toString());
        final String memberFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(memberShapeId, FROM_DAFNY);
        final String targetFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(targetShapeId, FROM_DAFNY);
        final List<ParseToken> expectedTokensFromDafny = Tokenizer.tokenize("""
                public static int %s(int value) {
                    return %s(value);
                }""".formatted(memberFromDafnyConverterName, targetFromDafnyConverterName));
        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);

        final List<ParseToken> actualTokensToDafny = Tokenizer.tokenize(converter.toDafny().toString());
        final String memberToDafnyConverterName = DotNetNameResolver.typeConverterForShape(memberShapeId, TO_DAFNY);
        final String targetToDafnyConverterName = DotNetNameResolver.typeConverterForShape(targetShapeId, TO_DAFNY);
        final List<ParseToken> expectedTokensToDafny = Tokenizer.tokenize("""
                public static int %s(int value) {
                    return %s(value);
                }""".formatted(memberToDafnyConverterName, targetToDafnyConverterName));
        assertEquals(expectedTokensToDafny, actualTokensToDafny);
    }

    @Test
    public void testGenerateMemberConverterOptional() {
        final ShapeId containerShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Container");
        final ShapeId memberShapeId = containerShapeId.withMember("content");
        final ShapeId targetShapeId = ShapeId.from("smithy.api#Integer");
        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
                modelAssembler.addUnparsedModel("test.smithy", """
                        namespace %s
                        structure Container {
                            content: Integer
                        }
                        """.formatted(SERVICE_NAMESPACE)));
        final TypeConverter converter = codegen.generateMemberConverter(
                codegen.getModel().expectShape(memberShapeId, MemberShape.class));
        assertEquals(memberShapeId, converter.shapeId());

        final List<ParseToken> actualTokensFromDafny = Tokenizer.tokenize(converter.fromDafny().toString());
        final String memberFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(memberShapeId, FROM_DAFNY);
        final String targetFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(targetShapeId, FROM_DAFNY);
        final List<ParseToken> expectedTokensFromDafny = Tokenizer.tokenize("""
                public static int? %s(Wrappers_Compile.Option<int> value) {
                    return value.is_None ? (int?) null : %s(value.Extract());
                }""".formatted(memberFromDafnyConverterName, targetFromDafnyConverterName));
        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);

        final List<ParseToken> actualTokensToDafny = Tokenizer.tokenize(converter.toDafny().toString());
        final String memberToDafnyConverterName = DotNetNameResolver.typeConverterForShape(memberShapeId, TO_DAFNY);
        final String targetToDafnyConverterName = DotNetNameResolver.typeConverterForShape(targetShapeId, TO_DAFNY);
        final List<ParseToken> expectedTokensToDafny = Tokenizer.tokenize("""
                public static Wrappers_Compile.Option<int> %s(int? value) {
                    return value == null
                        ? Wrappers_Compile.Option<int>.create_None()
                        : Wrappers_Compile.Option<int>.create_Some(%s((int) value));
                }""".formatted(memberToDafnyConverterName, targetToDafnyConverterName));
        assertEquals(expectedTokensToDafny, actualTokensToDafny);
    }
}
