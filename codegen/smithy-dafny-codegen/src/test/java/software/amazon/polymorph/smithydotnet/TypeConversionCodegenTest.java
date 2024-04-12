// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;
import static software.amazon.polymorph.smithydotnet.TypeConversionCodegen.TYPE_CONVERSION_CLASS_PATH;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.FROM_DAFNY;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.TO_DAFNY;
import static software.amazon.polymorph.util.TestModel.SERVICE_NAMESPACE;
import static software.amazon.polymorph.util.TestModel.SERVICE_SHAPE_ID;
import static software.amazon.polymorph.util.Tokenizer.tokenize;
import static software.amazon.polymorph.util.Tokenizer.tokenizeAndAssertEqual;

import java.nio.file.Path;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.junit.Test;
import software.amazon.polymorph.antlr.CSharpLexer;
import software.amazon.polymorph.smithydotnet.TypeConversionCodegen.TypeConverter;
import software.amazon.polymorph.traits.ClientConfigTrait;
import software.amazon.polymorph.util.TestModel;
import software.amazon.polymorph.util.Tokenizer.ParseToken;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.shapes.BlobShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;

public class TypeConversionCodegenTest {

  // TODO: Apply TypeConversionCodegen refactor to tests
  // https://github.com/smithy-lang/smithy-dafny/issues/29
  private static TypeConversionCodegen setupCodegen(
    final BiConsumer<ServiceShape.Builder, ModelAssembler> updater
  ) {
    final Model model = TestModel.setupModel(updater);
    final ServiceShape serviceShape = model.expectShape(
      SERVICE_SHAPE_ID,
      ServiceShape.class
    );
    return new TypeConversionCodegen(model, serviceShape);
  }

  private static String generate(final TypeConversionCodegen codegen) {
    final Map<Path, TokenTree> generatedCode = codegen.generate();
    assertTrue(generatedCode.containsKey(TYPE_CONVERSION_CLASS_PATH));
    return Objects
      .requireNonNull(generatedCode.get(TYPE_CONVERSION_CLASS_PATH))
      .toString();
  }

  // Removed 2023-01-27 for output-local-service-test
  //    @Test
  //    public void testGenerateEmptyModel() {
  //        final TypeConversionCodegen codegen = setupCodegen((_builder, _modelAssembler) -> {});
  //        final String actual = generate(codegen);
  //        final String expected = """
  //                using System.Linq;
  //                using System;
  //                namespace Test.Foobar {
  //                    internal static class TypeConversion {
  //                       public static System.Exception FromDafny_CommonError(test.foobar.internaldafny.types._IError value) {
  //                           switch (value) {
  //                               case test.foobar.internaldafny.types.Error_Opaque dafnyVal:
  //                                   return new OpaqueError(dafnyVal._obj);
  //                               default:
  //                                   // The switch MUST be complete for _IError, so `value` MUST NOT be an _IError. (How did you get here?)
  //                                   return new OpaqueError();
  //                           }
  //                       }
  //
  //                       public static test.foobar.internaldafny.types._IError ToDafny_CommonError(System.Exception value) {
  //                           switch (value) {
  //                               // OpaqueError is redundant, but listed for completeness.
  //                               case OpaqueError exception:
  //                                   return new test.foobar.internaldafny.types.Error_Opaque(exception);
  //                               case System.Exception exception:
  //                                   return new test.foobar.internaldafny.types.Error_Opaque(exception);
  //                               default:
  //                                   // The switch MUST be complete for System.Exception, so `value` MUST NOT be an System.Exception. (How did you get here?)
  //                                   return new test.foobar.internaldafny.types.Error_Opaque(value);
  //                           }
  //                       }
  //                    }
  //                }
  //                """.formatted(
  //                DotNetNameResolver.typeConverterForShape(ShapeId.from("smithy.api#String"), FROM_DAFNY),
  //                DotNetNameResolver.typeConverterForShape(ShapeId.from("smithy.api#String"), TO_DAFNY), //ToDafny_String
  //                DotNetNameResolver.typeConverterForShape(ShapeId.from("smithy.api#String"), TO_DAFNY)  //ToDafny_String
  //        );
  //        tokenizeAndAssertEqual(expected, actual);
  //    }

  @Test
  public void testGenerateSimpleModel() {
    final TypeConversionCodegen codegen = setupCodegen(
      (builder, modelAssembler) -> {
        builder.addOperation(ShapeId.fromParts(SERVICE_NAMESPACE, "DoBar"));
        modelAssembler.addUnparsedModel(
          "test.smithy",
          """
          namespace %s
          operation DoBar { input: DoBarInput, output: DoBarOutput }
          structure DoBarInput { bool: Boolean }
          structure DoBarOutput { int: Integer }
          """.formatted(SERVICE_NAMESPACE)
        );
      }
    );
    final String actual = generate(codegen);
    final Set<ParseToken> actualTokens = new HashSet<>(tokenize(actual));

    final Stream<ParseToken> expectedConverterMethods = Stream
      .of(
        SERVICE_NAMESPACE + "#DoBarInput",
        SERVICE_NAMESPACE + "#DoBarInput$bool",
        SERVICE_NAMESPACE + "#DoBarOutput",
        SERVICE_NAMESPACE + "#DoBarOutput$int",
        "smithy.api#Boolean",
        "smithy.api#Integer"
      )
      .map(ShapeId::from)
      .flatMap(shapeId ->
        Stream.of(
          DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY),
          DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY)
        )
      )
      .map(converterName ->
        new ParseToken(converterName, CSharpLexer.IDENTIFIER)
      );
    assertTrue(expectedConverterMethods.allMatch(actualTokens::contains));
  }

  @Test
  public void testFindShapeIdsToConvert() {
    final TypeConversionCodegen codegen = setupCodegen(
      (builder, modelAssembler) -> {
        builder.addOperation(ShapeId.fromParts(SERVICE_NAMESPACE, "DoBar"));
        builder.addTrait(
          ClientConfigTrait
            .builder()
            .clientConfigId(
              ShapeId.fromParts(SERVICE_NAMESPACE, "FoobarConfig")
            )
            .build()
        );
        modelAssembler.addUnparsedModel(
          "test.smithy",
          """
          namespace %s
          structure FoobarConfig {}
          resource FooResource { operations: [DoBaz] }
          operation DoBar { input: DoBarInput, errors: [UsedError] }
          operation DoBaz { output: DoBazOutput }
          structure DoBarInput { qux: Qux }
          structure DoBazOutput { xyzzy: Xyzzy }
          map Qux { key: String, value: Integer }
          list Xyzzy { member: Blob }
          @error("client") structure UsedError { @required message: String }
          @error("client") structure UnusedError { @required message: String }
          """.formatted(SERVICE_NAMESPACE)
        );
      }
    );
    final Set<ShapeId> expectedShapeIds = Stream
      .of(
        SERVICE_NAMESPACE + "#DoBarInput",
        SERVICE_NAMESPACE + "#DoBarInput$qux",
        SERVICE_NAMESPACE + "#DoBazOutput",
        SERVICE_NAMESPACE + "#DoBazOutput$xyzzy",
        SERVICE_NAMESPACE + "#Qux",
        SERVICE_NAMESPACE + "#Qux$key",
        SERVICE_NAMESPACE + "#Qux$value",
        SERVICE_NAMESPACE + "#Xyzzy",
        SERVICE_NAMESPACE + "#Xyzzy$member",
        SERVICE_NAMESPACE + "#UsedError",
        SERVICE_NAMESPACE + "#UsedError$message",
        // Unused errors must also have type converters, since the common error shape converter depends on all
        // specific errors in the model (even if unused in operations)
        SERVICE_NAMESPACE + "#UnusedError",
        SERVICE_NAMESPACE + "#UnusedError$message",
        "smithy.api#String",
        "smithy.api#Integer",
        "smithy.api#Blob"
      )
      .map(ShapeId::from)
      .collect(Collectors.toSet());

    final Set<ShapeId> actualShapeIds = codegen.findShapeIdsToConvert();
    assertEquals(expectedShapeIds, actualShapeIds);
  }

  @Test
  public void testGenerateBlobConverter() {
    final ShapeId shapeId = ShapeId.from("smithy.api#Blob");
    final TypeConversionCodegen codegen = setupCodegen(
      (_builder, _modelAssembler) -> {}
    );
    final TypeConverter converter = codegen.generateBlobConverter(
      BlobShape.builder().id(shapeId).build()
    );
    assertEquals(shapeId, converter.shapeId());

    final String actualFromDafny = converter.fromDafny().toString();
    final String fromDafnyConverterName =
      DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
    final String expectedFromDafny =
      """
      public static System.IO.MemoryStream %s(Dafny.ISequence<byte> value) {
          return new System.IO.MemoryStream(value.Elements);
      }
      """.formatted(fromDafnyConverterName);
    tokenizeAndAssertEqual(expectedFromDafny, actualFromDafny);

    final String actualToDafny = converter.toDafny().toString();
    final String toDafnyConverterName =
      DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
    final String expectedToDafny =
      """
      public static Dafny.ISequence<byte> %s(System.IO.MemoryStream value) {
          if (value.ToArray().Length == 0 && value.Length > 0)
          {
              throw new System.ArgumentException("Fatal Error: MemoryStream instance not backed by an array!");
          }
          return Dafny.Sequence<byte>.FromArray(value.ToArray());
      }
      """.formatted(toDafnyConverterName);
    tokenizeAndAssertEqual(expectedToDafny, actualToDafny);
  }

  //    @Test
  //    public void testGenerateBooleanConverter() {
  //        final ShapeId shapeId = ShapeId.from("smithy.api#Boolean");
  //        final TypeConversionCodegen codegen = setupCodegen((_builder, _modelAssembler) -> {});
  //        final TypeConverter converter = codegen.generateBooleanConverter(BooleanShape.builder().id(shapeId).build());
  //        assertEquals(shapeId, converter.shapeId());
  //
  //        final String actualFromDafny = converter.fromDafny().toString();
  //        final String fromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
  //        final String expectedFromDafny =
  //                "public static bool %s(bool value) { return value; }".formatted(fromDafnyConverterName);
  //        tokenizeAndAssertEqual(expectedFromDafny, actualFromDafny);
  //
  //        final String actualToDafny = converter.toDafny().toString();
  //        final String toDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
  //        final String expectedToDafny =
  //                "public static bool %s(bool value) { return value; }".formatted(toDafnyConverterName);
  //        tokenizeAndAssertEqual(expectedToDafny, actualToDafny);
  //    }

  //    @Test
  //    public void testGenerateStringConverterRegularString() {
  //        final ShapeId shapeId = ShapeId.from("smithy.api#String");
  //        final TypeConversionCodegen codegen = setupCodegen((_builder, _modelAssembler) -> {});
  //        final TypeConverter converter = codegen.generateStringConverter(StringShape.builder().id(shapeId).build());
  //        assertEquals(shapeId, converter.shapeId());
  //
  //        final String actualFromDafny = converter.fromDafny().toString();
  //        final String fromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
  //        final String expectedFromDafny = """
  //                public static string %s(Dafny.ISequence<char> value) {
  //                    return new string(value.Elements);
  //                }""".formatted(fromDafnyConverterName);
  //        tokenizeAndAssertEqual(expectedFromDafny, actualFromDafny);
  //
  //        final String actualToDafny = converter.toDafny().toString();
  //        final String toDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
  //        final String expectedToDafny = """
  //                public static Dafny.ISequence<char> %s(string value) {
  //                    return Dafny.Sequence<char>.FromString(value);
  //                }""".formatted(toDafnyConverterName);
  //        tokenizeAndAssertEqual(expectedToDafny, actualToDafny);
  //    }

  //    @Test
  //    public void testGenerateStringConverterEnumString() {
  //        final ShapeId shapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "AnEnum");
  //        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
  //                modelAssembler.addUnparsedModel("test.smithy", """
  //                        namespace %s
  //                        @enum([
  //                            { name: "VERSION_A", value: "bar" },
  //                            { name: "VERSION_B", value: "baz" },
  //                        ])
  //                        string AnEnum
  //                        """.formatted(SERVICE_NAMESPACE)));
  //        final TypeConverter converter = codegen.generateStringConverter(
  //                codegen.getModel().expectShape(shapeId, StringShape.class));
  //        assertEquals(shapeId, converter.shapeId());
  //
  //        final List<ParseToken> actualTokensFromDafny = tokenize(converter.fromDafny().toString());
  //        final String fromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
  //        final List<ParseToken> expectedTokensFromDafny = tokenize("""
  //                public static Test.Foobar.AnEnum %s(test.foobar.internaldafny.types._IAnEnum value) {
  //                    if (value.is_VERSION__A) return Test.Foobar.AnEnum.VERSION_A;
  //                    if (value.is_VERSION__B) return Test.Foobar.AnEnum.VERSION_B;
  //                    throw new System.ArgumentException("Invalid Test.Foobar.AnEnum value");
  //                }""".formatted(fromDafnyConverterName));
  //        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);
  //
  //        final List<ParseToken> actualTokensToDafny = tokenize(converter.toDafny().toString());
  //        final String toDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
  //        final List<ParseToken> expectedTokensToDafny = tokenize("""
  //                public static test.foobar.internaldafny.types._IAnEnum %s(Test.Foobar.AnEnum value) {
  //                    if (Test.Foobar.AnEnum.VERSION_A.Equals(value)) return test.foobar.internaldafny.types.AnEnum.create_VERSION__A();
  //                    if (Test.Foobar.AnEnum.VERSION_B.Equals(value)) return test.foobar.internaldafny.types.AnEnum.create_VERSION__B();
  //                    throw new System.ArgumentException("Invalid Test.Foobar.AnEnum value");
  //                }""".formatted(toDafnyConverterName));
  //        assertEquals(expectedTokensToDafny, actualTokensToDafny);
  //    }
  //
  //    /**
  //     * Test that we generate an enum converter correctly when the enum has only one constructor.
  //     *
  //     * This is different than the "normal" case because Dafny doesn't generate a compiled constructor when there's only
  //     * one.
  //     */
  //    @Test
  //    public void testGenerateStringConverterEnumStringSingleConstructor() {
  //        final ShapeId shapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "AnEnum");
  //        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
  //                modelAssembler.addUnparsedModel("test.smithy", """
  //                        namespace %s
  //                        @enum([{ name: "VERSION_A", value: "bar" }])
  //                        string AnEnum
  //                        """.formatted(SERVICE_NAMESPACE)));
  //        final TypeConverter converter = codegen.generateStringConverter(
  //                codegen.getModel().expectShape(shapeId, StringShape.class));
  //        assertEquals(shapeId, converter.shapeId());
  //
  //        final List<ParseToken> actualTokensFromDafny = tokenize(converter.fromDafny().toString());
  //        final String fromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
  //        final List<ParseToken> expectedTokensFromDafny = tokenize("""
  //                public static Test.Foobar.AnEnum %s(test.foobar.internaldafny.types._IAnEnum value) {
  //                    if (value.is_VERSION__A) return Test.Foobar.AnEnum.VERSION_A;
  //                    throw new System.ArgumentException("Invalid Test.Foobar.AnEnum value");
  //                }""".formatted(fromDafnyConverterName));
  //        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);
  //
  //        final List<ParseToken> actualTokensToDafny = tokenize(converter.toDafny().toString());
  //        final String toDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
  //        final List<ParseToken> expectedTokensToDafny = tokenize("""
  //                public static test.foobar.internaldafny.types._IAnEnum %s(Test.Foobar.AnEnum value) {
  //                    if (Test.Foobar.AnEnum.VERSION_A.Equals(value)) return test.foobar.internaldafny.types.AnEnum.create();
  //                    throw new System.ArgumentException("Invalid Test.Foobar.AnEnum value");
  //                }""".formatted(toDafnyConverterName));
  //        assertEquals(expectedTokensToDafny, actualTokensToDafny);
  //    }

  //    @Test
  //    public void testGenerateStringConverterUtf8Bytes() {
  //        final ShapeId shapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Utf8BytesString");
  //        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
  //                modelAssembler.addUnparsedModel("test.smithy", """
  //                        namespace %s
  //                        use aws.polymorph#dafnyUtf8Bytes
  //                        @dafnyUtf8Bytes
  //                        string Utf8BytesString
  //                        """.formatted(SERVICE_NAMESPACE)));
  //        final TypeConverter converter = codegen.generateStringConverter(
  //                codegen.getModel().expectShape(shapeId, StringShape.class));
  //        assertEquals(shapeId, converter.shapeId());
  //
  //        final List<ParseToken> actualTokensFromDafny = tokenize(converter.fromDafny().toString());
  //        final String fromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
  //        final List<ParseToken> expectedTokensFromDafny = tokenize("""
  //                public static string %s(Dafny.ISequence<byte> value) {
  //                    System.Text.UTF8Encoding utf8 = new System.Text.UTF8Encoding(false, true);
  //                    return utf8.GetString(value.Elements);
  //                }""".formatted(fromDafnyConverterName));
  //        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);
  //
  //        final List<ParseToken> actualTokensToDafny = tokenize(converter.toDafny().toString());
  //        final String toDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
  //        final List<ParseToken> expectedTokensToDafny = tokenize("""
  //                public static Dafny.ISequence<byte> %s(string value) {
  //                    System.Text.UTF8Encoding utf8 = new System.Text.UTF8Encoding(false, true);
  //                    return Dafny.Sequence<byte>.FromArray(utf8.GetBytes(value));
  //                }""".formatted(toDafnyConverterName));
  //        assertEquals(expectedTokensToDafny, actualTokensToDafny);
  //    }

  //    @Test
  //    public void testGenerateIntegerConverter() {
  //        final ShapeId shapeId = ShapeId.from("smithy.api#Integer");
  //        final TypeConversionCodegen codegen = setupCodegen((_builder, _modelAssembler) -> {});
  //        final TypeConverter converter = codegen.generateIntegerConverter(IntegerShape.builder().id(shapeId).build());
  //        assertEquals(shapeId, converter.shapeId());
  //
  //        final List<ParseToken> actualTokensFromDafny = tokenize(converter.fromDafny().toString());
  //        final String fromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
  //        final List<ParseToken> expectedTokensFromDafny = tokenize(
  //                "public static int %s(int value) { return value; }".formatted(fromDafnyConverterName));
  //        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);
  //
  //        final List<ParseToken> actualTokensToDafny = tokenize(converter.toDafny().toString());
  //        final String toDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
  //        final List<ParseToken> expectedTokensToDafny = tokenize(
  //                "public static int %s(int value) { return value; }".formatted(toDafnyConverterName));
  //        assertEquals(expectedTokensToDafny, actualTokensToDafny);
  //    }

  //    @Test
  //    public void testGenerateLongConverter() {
  //        final ShapeId shapeId = ShapeId.from("smithy.api#Long");
  //        final TypeConversionCodegen codegen = setupCodegen((_builder, _modelAssembler) -> {});
  //        final TypeConverter converter = codegen.generateLongConverter(LongShape.builder().id(shapeId).build());
  //        assertEquals(shapeId, converter.shapeId());
  //
  //        final List<ParseToken> actualTokensFromDafny = tokenize(converter.fromDafny().toString());
  //        final String fromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
  //        final List<ParseToken> expectedTokensFromDafny = tokenize(
  //                "public static long %s(long value) { return value; }".formatted(fromDafnyConverterName));
  //        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);
  //
  //        final List<ParseToken> actualTokensToDafny = tokenize(converter.toDafny().toString());
  //        final String toDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
  //        final List<ParseToken> expectedTokensToDafny = tokenize(
  //                "public static long %s(long value) { return value; }".formatted(toDafnyConverterName));
  //        assertEquals(expectedTokensToDafny, actualTokensToDafny);
  //    }

  //    @Test
  //    public void testGenerateTimestampConverter() {
  //        final ShapeId shapeId = ShapeId.from("smithy.api#Timestamp");
  //        final TypeConversionCodegen codegen = setupCodegen((_builder, _modelAssembler) -> {});
  //        final TypeConverter converter = codegen.generateTimestampConverter(
  //                TimestampShape.builder().id(shapeId).build());
  //        assertEquals(shapeId, converter.shapeId());
  //
  //        final List<ParseToken> actualTokensFromDafny = tokenize(converter.fromDafny().toString());
  //        final String fromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
  //        final List<ParseToken> expectedTokensFromDafny = tokenize("""
  //                public static System.DateTime %s(Dafny.ISequence<char> value) {
  //                    System.Globalization.CultureInfo culture = new System.Globalization.CultureInfo("");
  //                    string timestampString = new string(value.Elements);
  //                    return System.DateTime.ParseExact(timestampString, "s", culture);
  //                }
  //                """.formatted(fromDafnyConverterName));
  //        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);
  //
  //        final List<ParseToken> actualTokensToDafny = tokenize(converter.toDafny().toString());
  //        final String toDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
  //        final List<ParseToken> expectedTokensToDafny = tokenize("""
  //                public static Dafny.ISequence<char> %s(System.DateTime value) {
  //                    System.Globalization.CultureInfo culture = new System.Globalization.CultureInfo("");
  //                    string timestampString = value.ToString("s", culture);
  //                    return Dafny.Sequence<char>.FromString(timestampString);
  //                }
  //                """.formatted(toDafnyConverterName));
  //        assertEquals(expectedTokensToDafny, actualTokensToDafny);
  //    }

  //    @Test
  //    public void testGenerateListConverter() {
  //        final ShapeId shapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "IntList");
  //        final ShapeId memberShapeId = shapeId.withMember("member");
  //        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
  //                modelAssembler.addUnparsedModel("test.smithy", """
  //                        namespace %s
  //                        list IntList {
  //                            member: Integer
  //                        }
  //                        """.formatted(SERVICE_NAMESPACE)));
  //        final TypeConverter converter = codegen.generateListConverter(
  //                codegen.getModel().expectShape(shapeId, ListShape.class));
  //        assertEquals(shapeId, converter.shapeId());
  //
  //        final List<ParseToken> actualTokensFromDafny = tokenize(converter.fromDafny().toString());
  //        final String listFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
  //        final String intFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(memberShapeId, FROM_DAFNY);
  //        final List<ParseToken> expectedTokensFromDafny = tokenize("""
  //                public static System.Collections.Generic.List<int> %s(Dafny.ISequence<int> value) {
  //                    return new System.Collections.Generic.List<int>(value.Elements.Select(%s));
  //                }""".formatted(listFromDafnyConverterName, intFromDafnyConverterName));
  //        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);
  //
  //        final List<ParseToken> actualTokensToDafny = tokenize(converter.toDafny().toString());
  //        final String listToDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
  //        final String intToDafnyConverterName = DotNetNameResolver.typeConverterForShape(memberShapeId, TO_DAFNY);
  //        final List<ParseToken> expectedTokensToDafny = tokenize("""
  //                public static Dafny.ISequence<int> %s(System.Collections.Generic.List<int> value) {
  //                    return Dafny.Sequence<int>.FromArray(value.Select(%s).ToArray());
  //                }""".formatted(listToDafnyConverterName, intToDafnyConverterName));
  //        assertEquals(expectedTokensToDafny, actualTokensToDafny);
  //    }

  //    @Test
  //    public void testGenerateMapConverter() {
  //        final ShapeId shapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "BoolMap");
  //        final ShapeId keyMemberId = shapeId.withMember("key");
  //        final ShapeId valueMemberId = shapeId.withMember("value");
  //        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
  //                modelAssembler.addUnparsedModel("test.smithy", """
  //                        namespace %s
  //                        map BoolMap {
  //                            key: String,
  //                            value: Boolean,
  //                        }
  //                        """.formatted(SERVICE_NAMESPACE)));
  //        final TypeConverter converter = codegen.generateMapConverter(
  //                codegen.getModel().expectShape(shapeId, MapShape.class));
  //        assertEquals(shapeId, converter.shapeId());
  //
  //        final List<ParseToken> actualTokensFromDafny = tokenize(converter.fromDafny().toString());
  //        final String mapFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
  //        final String keyFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(keyMemberId, FROM_DAFNY);
  //        final String valueFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(valueMemberId, FROM_DAFNY);
  //        final List<ParseToken> expectedTokensFromDafny = tokenize("""
  //                public static System.Collections.Generic.Dictionary<string, bool> %s(
  //                        Dafny.IMap<Dafny.ISequence<char>, bool> value) {
  //                    return value.ItemEnumerable.ToDictionary(pair => %s(pair.Car), pair => %s(pair.Cdr));
  //                }""".formatted(mapFromDafnyConverterName, keyFromDafnyConverterName, valueFromDafnyConverterName));
  //        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);
  //
  //        final List<ParseToken> actualTokensToDafny = tokenize(converter.toDafny().toString());
  //        final String mapToDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
  //        final String keyToDafnyConverterName = DotNetNameResolver.typeConverterForShape(keyMemberId, TO_DAFNY);
  //        final String valueToDafnyConverterName = DotNetNameResolver.typeConverterForShape(valueMemberId, TO_DAFNY);
  //        final List<ParseToken> expectedTokensToDafny = tokenize("""
  //                public static Dafny.IMap<Dafny.ISequence<char>, bool> %s(
  //                        System.Collections.Generic.Dictionary<string, bool> value) {
  //                    return Dafny.Map<Dafny.ISequence<char>, bool>.FromCollection(
  //                        value.Select(pair =>
  //                            new Dafny.Pair<Dafny.ISequence<char>, bool>(%s(pair.Key), %s(pair.Value))
  //                        )
  //                    );
  //                }""".formatted(mapToDafnyConverterName, keyToDafnyConverterName, valueToDafnyConverterName));
  //        assertEquals(expectedTokensToDafny, actualTokensToDafny);
  //    }

  //    @Test
  //    public void testGenerateStructureConverterRegularStructure() {
  //        final ShapeId shapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "IntAndBool");
  //        final ShapeId intMemberId = shapeId.withMember("someInt");
  //        final ShapeId boolMemberId = shapeId.withMember("someBool");
  //        final ShapeId stringMemberId = shapeId.withMember("someString");
  //        final ShapeId refMemberId = shapeId.withMember("someRef");
  //        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
  //                modelAssembler.addUnparsedModel("test.smithy", """
  //                        namespace %s
  //                        use aws.polymorph#reference
  //                        resource Thing {}
  //                        @reference(resource: Thing)
  //                        structure ThingReference {}
  //
  //                        structure IntAndBool {
  //                            someInt: Integer,
  //                            @required
  //                            someBool: Boolean,
  //                            someString: String,
  //                            someRef: ThingReference,
  //                        }
  //                        """.formatted(SERVICE_NAMESPACE)));
  //        final TypeConverter converter = codegen.generateStructureConverter(
  //                codegen.getModel().expectShape(shapeId, StructureShape.class));
  //        assertEquals(shapeId, converter.shapeId());
  //
  //        final List<ParseToken> actualTokensFromDafny = tokenize(converter.fromDafny().toString());
  //        final String structureFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
  //        final String intFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(intMemberId, FROM_DAFNY);
  //        final String boolFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(boolMemberId, FROM_DAFNY);
  //        final String stringFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(stringMemberId, FROM_DAFNY);
  //        final String refFromDafnyConverterName = DotNetNameResolver
  //            .typeConverterForShape(refMemberId, FROM_DAFNY);
  //        final List<ParseToken> expectedTokensFromDafny = tokenize("""
  //                public static Test.Foobar.IntAndBool %s(test.foobar.internaldafny.types._IIntAndBool value) {
  //                    test.foobar.internaldafny.types.IntAndBool concrete = (test.foobar.internaldafny.types.IntAndBool)value;
  //                    Test.Foobar.IntAndBool converted = new Test.Foobar.IntAndBool();
  //                    if (concrete._someInt.is_Some) converted.SomeInt = (int) %s(concrete._someInt);
  //                    converted.SomeBool = (bool) %s(concrete._someBool);
  //                    if (concrete._someString.is_Some) converted.SomeString = (string) %s(concrete._someString);
  //                    if (concrete._someRef.is_Some) converted.SomeRef = (Test.Foobar.IThing) %s(concrete._someRef);
  //                    return converted;
  //                }""".formatted(
  //                        structureFromDafnyConverterName,
  //                        intFromDafnyConverterName,
  //                        boolFromDafnyConverterName,
  //                        stringFromDafnyConverterName,
  //                        refFromDafnyConverterName));
  //        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);
  //
  //        final List<ParseToken> actualTokensToDafny = tokenize(converter.toDafny().toString());
  //        final String structureToDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
  //        final String intToDafnyConverterName = DotNetNameResolver.typeConverterForShape(intMemberId, TO_DAFNY);
  //        final String boolToDafnyConverterName = DotNetNameResolver.typeConverterForShape(boolMemberId, TO_DAFNY);
  //        final String stringToDafnyConverterName = DotNetNameResolver.typeConverterForShape(stringMemberId, TO_DAFNY);
  //        final String refToDafnyConverterName = DotNetNameResolver
  //                .typeConverterForShape(refMemberId, TO_DAFNY);
  //        final List<ParseToken> expectedTokensToDafny = tokenize("""
  //                public static test.foobar.internaldafny.types._IIntAndBool %s(Test.Foobar.IntAndBool value) {
  //                    int? var_someInt = value.IsSetSomeInt() ? value.SomeInt : (int?) null;
  //                    string var_someString = value.IsSetSomeString() ? value.SomeString : (string) null;
  //                    Test.Foobar.IThing var_someRef = value.IsSetSomeRef() ? value.SomeRef : (Test.Foobar.IThing) null;
  //                    return new test.foobar.internaldafny.types.IntAndBool(
  //                        %s(var_someInt),
  //                        %s(value.SomeBool),
  //                        %s(var_someString),
  //                        %s(var_someRef)
  //                    );
  //                }""".formatted(
  //                        structureToDafnyConverterName,
  //                        intToDafnyConverterName,
  //                        boolToDafnyConverterName,
  //                        stringToDafnyConverterName,
  //                        refToDafnyConverterName));
  //        assertEquals(expectedTokensToDafny, actualTokensToDafny);
  //    }

  @Test
  public void testGenerateStructureConverterReferenceStructure() {
    final ShapeId shapeId = ShapeId.fromParts(
      SERVICE_NAMESPACE,
      "ThingReference"
    );
    final TypeConversionCodegen codegen = setupCodegen(
        (builder, modelAssembler) ->
      modelAssembler.addUnparsedModel(
        "test.smithy",
        """
        namespace %s
        use aws.polymorph#reference
        resource Thing {}
        @reference(resource: Thing)
        structure ThingReference {}
        """.formatted(SERVICE_NAMESPACE)
      )
    );
    final TypeConverter converter = codegen.generateStructureConverter(
      codegen.getModel().expectShape(shapeId, StructureShape.class)
    );
    assertEquals(shapeId, converter.shapeId());

    final List<ParseToken> actualTokensFromDafny = tokenize(
      converter.fromDafny().toString()
    );
    final String structureFromDafnyConverterName =
      DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
    final List<ParseToken> expectedTokensFromDafny = tokenize(
      """
      public static Test.Foobar.IThing %s(test.foobar.internaldafny.types.IThing value) {
          return new Thing(value);
      }""".formatted(structureFromDafnyConverterName)
    );
    assertEquals(expectedTokensFromDafny, actualTokensFromDafny);

    final List<ParseToken> actualTokensToDafny = tokenize(
      converter.toDafny().toString()
    );
    final String structureToDafnyConverterName =
      DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
    final List<ParseToken> expectedTokensToDafny = tokenize(
      """
      public static test.foobar.internaldafny.types.IThing %s(Test.Foobar.IThing value) {
          if (value is Thing valueWithImpl) {
              return valueWithImpl._impl;
          }
          throw new System.ArgumentException(
              "Custom implementations of Test.Foobar.IThing are not supported");
      }""".formatted(structureToDafnyConverterName)
    );
    assertEquals(expectedTokensToDafny, actualTokensToDafny);
  }

  @Test
  public void testGenerateStructureConverterExtendableStructure() {
    final ShapeId shapeId = ShapeId.fromParts(
      SERVICE_NAMESPACE,
      "ThingReference"
    );
    final TypeConversionCodegen codegen = setupCodegen(
        (builder, modelAssembler) ->
      modelAssembler.addUnparsedModel(
        "test.smithy",
        """
        namespace %s
        use aws.polymorph#extendable
        use aws.polymorph#reference
        @extendable
        resource Thing {}
        @reference(resource: Thing)
        structure ThingReference {}
        """.formatted(SERVICE_NAMESPACE)
      )
    );
    final TypeConverter converter = codegen.generateStructureConverter(
      codegen.getModel().expectShape(shapeId, StructureShape.class)
    );
    assertEquals(shapeId, converter.shapeId());
    final String actualFromDafny = converter.fromDafny().toString();
    final String structureFromDafnyConverterName =
      DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
    final String expectedFromDafny =
      """
      public static Test.Foobar.IThing %s(test.foobar.internaldafny.types.IThing value) {
          if (value is NativeWrapper_Thing nativeWrapper) return nativeWrapper._impl;
          return new Thing(value);
      }
      """.formatted(structureFromDafnyConverterName);
    tokenizeAndAssertEqual(expectedFromDafny, actualFromDafny);

    final String actualToDafny = converter.toDafny().toString();
    final String structureToDafnyConverterName =
      DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
    final String expectedToDafny =
      """
      public static test.foobar.internaldafny.types.IThing %s(Test.Foobar.IThing value) {
          switch (value)
          {
              case Thing valueWithImpl:
                  return valueWithImpl._impl;
              case ThingBase nativeImpl:
                  return new NativeWrapper_Thing(nativeImpl);
              default:
                  throw new System.ArgumentException(
                       "Custom implementations of Thing must extend ThingBase.");
          }
      }""".formatted(structureToDafnyConverterName);
    tokenizeAndAssertEqual(expectedToDafny, actualToDafny);
  }
  //    @Test
  //    public void testGenerateStructureConverterPositionalStructure() {
  //        final ShapeId shapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "CreateThingOutput");
  //        final ShapeId memberShapeId = shapeId.withMember("thing");
  //        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
  //                modelAssembler.addUnparsedModel("test.smithy", """
  //                        namespace %s
  //                        use aws.polymorph#positional
  //                        use aws.polymorph#reference
  //                        resource Thing {}
  //                        @reference(resource: Thing)
  //                        structure ThingReference {}
  //                        @positional
  //                        structure CreateThingOutput { thing: ThingReference }
  //                        """.formatted(SERVICE_NAMESPACE)));
  //        final TypeConverter converter = codegen.generateStructureConverter(
  //                codegen.getModel().expectShape(shapeId, StructureShape.class));
  //        assertEquals(shapeId, converter.shapeId());
  //
  //        final List<ParseToken> actualTokensFromDafny = tokenize(converter.fromDafny().toString());
  //        final String structureFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, FROM_DAFNY);
  //        final String memberFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(memberShapeId, FROM_DAFNY);
  //        final List<ParseToken> expectedTokensFromDafny = tokenize("""
  //                public static Test.Foobar.IThing %s(test.foobar.internaldafny.types.IThing value) {
  //                    return %s(value);
  //                }""".formatted(structureFromDafnyConverterName, memberFromDafnyConverterName));
  //        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);
  //
  //        final List<ParseToken> actualTokensToDafny = tokenize(converter.toDafny().toString());
  //        final String structureToDafnyConverterName = DotNetNameResolver.typeConverterForShape(shapeId, TO_DAFNY);
  //        final String memberToDafnyConverterName = DotNetNameResolver.typeConverterForShape(memberShapeId, TO_DAFNY);
  //        final List<ParseToken> expectedTokensToDafny = tokenize("""
  //                public static test.foobar.internaldafny.types.IThing %s(Test.Foobar.IThing value) {
  //                    return %s(value);
  //                }""".formatted(structureToDafnyConverterName, memberToDafnyConverterName));
  //        assertEquals(expectedTokensToDafny, actualTokensToDafny);
  //    }

  //    @Test
  //    public void testGenerateMemberConverterRequired() {
  //        final ShapeId containerShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Container");
  //        final ShapeId memberShapeId = containerShapeId.withMember("content");
  //        final ShapeId targetShapeId = ShapeId.from("smithy.api#Integer");
  //        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
  //                modelAssembler.addUnparsedModel("test.smithy", """
  //                        namespace %s
  //                        structure Container {
  //                            @required
  //                            content: Integer
  //                        }
  //                        """.formatted(SERVICE_NAMESPACE)));
  //        final TypeConverter converter = codegen.generateMemberConverter(
  //                codegen.getModel().expectShape(memberShapeId, MemberShape.class));
  //        assertEquals(memberShapeId, converter.shapeId());
  //
  //        final List<ParseToken> actualTokensFromDafny = tokenize(converter.fromDafny().toString());
  //        final String memberFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(memberShapeId, FROM_DAFNY);
  //        final String targetFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(targetShapeId, FROM_DAFNY);
  //        final List<ParseToken> expectedTokensFromDafny = tokenize("""
  //                public static int %s(int value) {
  //                    return %s(value);
  //                }""".formatted(memberFromDafnyConverterName, targetFromDafnyConverterName));
  //        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);
  //
  //        final List<ParseToken> actualTokensToDafny = tokenize(converter.toDafny().toString());
  //        final String memberToDafnyConverterName = DotNetNameResolver.typeConverterForShape(memberShapeId, TO_DAFNY);
  //        final String targetToDafnyConverterName = DotNetNameResolver.typeConverterForShape(targetShapeId, TO_DAFNY);
  //        final List<ParseToken> expectedTokensToDafny = tokenize("""
  //                public static int %s(int value) {
  //                    return %s(value);
  //                }""".formatted(memberToDafnyConverterName, targetToDafnyConverterName));
  //        assertEquals(expectedTokensToDafny, actualTokensToDafny);
  //    }

  //    @Test
  //    public void testGenerateMemberConverterOptional() {
  //        final ShapeId containerShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Container");
  //        final ShapeId memberShapeId = containerShapeId.withMember("content");
  //        final ShapeId targetShapeId = ShapeId.from("smithy.api#Integer");
  //        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
  //                modelAssembler.addUnparsedModel("test.smithy", """
  //                        namespace %s
  //                        structure Container {
  //                            content: Integer
  //                        }
  //                        """.formatted(SERVICE_NAMESPACE)));
  //        final TypeConverter converter = codegen.generateMemberConverter(
  //                codegen.getModel().expectShape(memberShapeId, MemberShape.class));
  //        assertEquals(memberShapeId, converter.shapeId());
  //
  //        final List<ParseToken> actualTokensFromDafny = tokenize(converter.fromDafny().toString());
  //        final String memberFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(memberShapeId, FROM_DAFNY);
  //        final String targetFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(targetShapeId, FROM_DAFNY);
  //        final List<ParseToken> expectedTokensFromDafny = tokenize("""
  //                public static int? %s(Wrappers_Compile._IOption<int> value) {
  //                    return value.is_None ? (int?) null : %s(value.Extract());
  //                }""".formatted(memberFromDafnyConverterName, targetFromDafnyConverterName));
  //        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);
  //
  //        final List<ParseToken> actualTokensToDafny = tokenize(converter.toDafny().toString());
  //        final String memberToDafnyConverterName = DotNetNameResolver.typeConverterForShape(memberShapeId, TO_DAFNY);
  //        final String targetToDafnyConverterName = DotNetNameResolver.typeConverterForShape(targetShapeId, TO_DAFNY);
  //        final List<ParseToken> expectedTokensToDafny = tokenize("""
  //                public static Wrappers_Compile._IOption<int> %s(int? value) {
  //                    return value == null
  //                        ? Wrappers_Compile.Option<int>.create_None()
  //                        : Wrappers_Compile.Option<int>.create_Some(%s((int) value));
  //                }""".formatted(memberToDafnyConverterName, targetToDafnyConverterName));
  //        assertEquals(expectedTokensToDafny, actualTokensToDafny);
  //    }

  //    @Test
  //    public void testGenerateMemberConverterOptionalReference() {
  //        final ShapeId containerShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Container");
  //        final ShapeId memberShapeId = containerShapeId.withMember("ref");
  //        final ShapeId targetShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "ThingReference");
  //        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
  //                modelAssembler.addUnparsedModel("test.smithy", """
  //                        namespace %s
  //                        use aws.polymorph#reference
  //                        resource Thing {}
  //                        @reference(resource: Thing)
  //                        structure ThingReference {}
  //                        structure Container {
  //                            ref: ThingReference
  //                        }
  //                        """.formatted(SERVICE_NAMESPACE)));
  //        final TypeConverter converter = codegen.generateMemberConverter(
  //                codegen.getModel().expectShape(memberShapeId, MemberShape.class));
  //        assertEquals(memberShapeId, converter.shapeId());
  //
  //        final List<ParseToken> actualTokensFromDafny = tokenize(converter.fromDafny().toString());
  //        final String memberFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(memberShapeId, FROM_DAFNY);
  //        final String targetFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(targetShapeId, FROM_DAFNY);
  //        final List<ParseToken> expectedTokensFromDafny = tokenize("""
  //                public static Test.Foobar.IThing %s(Wrappers_Compile._IOption<test.foobar.internaldafny.types.IThing> value) {
  //                    return value.is_None ? (Test.Foobar.IThing) null : %s(value.Extract());
  //                }""".formatted(memberFromDafnyConverterName, targetFromDafnyConverterName));
  //        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);
  //
  //        final List<ParseToken> actualTokensToDafny = tokenize(converter.toDafny().toString());
  //        final String memberToDafnyConverterName = DotNetNameResolver.typeConverterForShape(memberShapeId, TO_DAFNY);
  //        final String targetToDafnyConverterName = DotNetNameResolver.typeConverterForShape(targetShapeId, TO_DAFNY);
  //        final List<ParseToken> expectedTokensToDafny = tokenize("""
  //                public static Wrappers_Compile._IOption<test.foobar.internaldafny.types.IThing> %s(Test.Foobar.IThing value) {
  //                    return value == null
  //                        ? Wrappers_Compile.Option<test.foobar.internaldafny.types.IThing>.create_None()
  //                        : Wrappers_Compile.Option<test.foobar.internaldafny.types.IThing>.create_Some(%s((Test.Foobar.IThing) value));
  //                }""".formatted(memberToDafnyConverterName, targetToDafnyConverterName));
  //        assertEquals(expectedTokensToDafny, actualTokensToDafny);
  //    }

  //    @Test
  //    public void testGenerateSpecificExceptionConverter() {
  //        final ShapeId errorShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "UnfortunateError");
  //        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
  //                modelAssembler.addUnparsedModel("test.smithy", """
  //                        namespace %s
  //                        @error("client")
  //                        structure UnfortunateError {
  //                            @required
  //                            message: String
  //                        }
  //                        """.formatted(SERVICE_NAMESPACE)));
  //        final TypeConverter converter = codegen.generateSpecificExceptionConverter(
  //                codegen.getModel().expectShape(errorShapeId, StructureShape.class));
  //        assertEquals(errorShapeId, converter.shapeId());
  //
  //        final String messageFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(errorShapeId.withMember("message"), FROM_DAFNY);
  //        final String messageToDafnyConverterName = DotNetNameResolver.typeConverterForShape(errorShapeId.withMember("message"), TO_DAFNY);
  //        final String errorFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(errorShapeId, FROM_DAFNY);
  //        final String errorToDafnyConverterName = DotNetNameResolver.typeConverterForShape(errorShapeId, TO_DAFNY);
  //
  //        final List<ParseToken> actualTokensFromDafny = tokenize(converter.fromDafny().toString());
  //        final List<ParseToken> expectedTokensFromDafny = tokenize("""
  //                public static Test.Foobar.UnfortunateError %s(test.foobar.internaldafny.types.Error_UnfortunateError value) {
  //                    return new Test.Foobar.UnfortunateError(%s(value.message));
  //                }""".formatted(errorFromDafnyConverterName, messageFromDafnyConverterName));
  //        assertEquals(expectedTokensFromDafny, actualTokensFromDafny);
  //
  //        final List<ParseToken> actualTokensToDafny = tokenize(converter.toDafny().toString());
  //        final List<ParseToken> expectedTokensToDafny = tokenize("""
  //                public static test.foobar.internaldafny.types.Error_UnfortunateError %s(Test.Foobar.UnfortunateError value) {
  //                    test.foobar.internaldafny.types.Error_UnfortunateError converted = new test.foobar.internaldafny.types.Error_UnfortunateError();
  //                    converted.message = %s(value.Message);
  //                    return converted;
  //                }""".formatted(errorToDafnyConverterName, messageToDafnyConverterName));
  //        assertEquals(expectedTokensToDafny, actualTokensToDafny);
  //    }
  //
  //    @Test
  //    public void testGenerateCommonExceptionConverter() {
  //        final ShapeId exc1ShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Exception1");
  //        final ShapeId exc2ShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Exception2");
  //        final TypeConversionCodegen codegen = setupCodegen((builder, modelAssembler) ->
  //            modelAssembler.addUnparsedModel("test.smithy", """
  //                namespace %s
  //                @error("client")
  //                structure Exception1 { @required message: String }
  //                @error("server")
  //                structure Exception2 { @required message: String }
  //                """.formatted(SERVICE_NAMESPACE)));
  //        final TypeConverter converter = codegen.generateCommonExceptionConverter();
  //        assertTrue("Common exception converter must use a shape ID not in the model",
  //            codegen.getModel().getShape(converter.shapeId()).isEmpty());
  //
  //        final String actualFromDafny = converter.fromDafny().toString();
  //        final String expectedFromDafny = """
  //            public static System.Exception FromDafny_CommonError(test.foobar.internaldafny.types._IError value) {
  //                switch (value) {
  //                    case test.foobar.internaldafny.types.Error_Exception1 dafnyVal:
  //                        return %s(dafnyVal);
  //                    case test.foobar.internaldafny.types.Error_Exception2 dafnyVal:
  //                        return %s(dafnyVal);
  //                    case test.foobar.internaldafny.types.Error_Opaque dafnyVal:
  //                        return new OpaqueError(dafnyVal._obj);
  //                    default:
  //                        // The switch MUST be complete for _IError, so `value` MUST NOT be an _IError. (How did you get here?)
  //                        return new OpaqueError();
  //                }
  //            }""".formatted(
  //            DotNetNameResolver.typeConverterForShape(exc1ShapeId, FROM_DAFNY),
  //            DotNetNameResolver.typeConverterForShape(exc2ShapeId, FROM_DAFNY)
  //        );
  //        tokenizeAndAssertEqual(expectedFromDafny, actualFromDafny);
  //
  //
  //        final String actualToDafny = converter.toDafny().toString();
  //        final String expectedToDafny = """
  //            public static test.foobar.internaldafny.types._IError ToDafny_CommonError(System.Exception value) {
  //                switch (value) {
  //                    case Test.Foobar.Exception1 exception:
  //                        return %s(exception);
  //                    case Test.Foobar.Exception2 exception:
  //                        return %s(exception);
  //                    // OpaqueError is redundant, but listed for completeness.
  //                    case OpaqueError exception:
  //                        return new test.foobar.internaldafny.types.Error_Opaque(exception);
  //                    case System.Exception exception:
  //                        return new test.foobar.internaldafny.types.Error_Opaque(exception);
  //                    default:
  //                        // The switch MUST be complete for System.Exception, so `value` MUST NOT be an System.Exception. (How did you get here?)
  //                        return new test.foobar.internaldafny.types.Error_Opaque(value);
  //                }
  //            }""".formatted(DotNetNameResolver.typeConverterForShape(exc1ShapeId, TO_DAFNY),
  //                           DotNetNameResolver.typeConverterForShape(exc2ShapeId, TO_DAFNY)
  //        );
  //
  //        tokenizeAndAssertEqual(expectedToDafny, actualToDafny);
  // }
}
