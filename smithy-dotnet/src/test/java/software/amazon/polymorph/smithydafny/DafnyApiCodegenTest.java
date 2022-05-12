// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydafny;

import org.junit.Test;
import software.amazon.polymorph.util.TestModel;
import software.amazon.polymorph.util.Tokenizer;
import software.amazon.polymorph.util.Tokenizer.ParseToken;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;

import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.function.BiConsumer;

import static org.junit.Assert.*;
import static software.amazon.polymorph.util.TestModel.SERVICE_NAMESPACE;
import static software.amazon.polymorph.util.TestModel.SERVICE_SHAPE_ID;

// TODO: use Dafny tokenizer instead of C# tokenizer
public class DafnyApiCodegenTest {
    private static DafnyApiCodegen setupCodegen(final BiConsumer<ServiceShape.Builder, ModelAssembler> updater) {
        final Model model = TestModel.setupModel(updater);
        return new DafnyApiCodegen(model, SERVICE_SHAPE_ID);
    }

    @Test
    public void testGenerate() {
        final ShapeId operationShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "DoIt");
        final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) -> {
            builder.addOperation(operationShapeId);
            modelAssembler.addUnparsedModel("test.smithy", """
                    namespace %s
                    operation DoIt {}
                    boolean SomeBool
                    @enum([{name: "A", value: "A"}, {name: "B", value: "B"}]) string SomeEnum
                    long SomeLong
                    list SomeList { member: String }
                    structure SomeStructure { someInt: Integer }
                    map EncryptionContextType { key: EncryptionContextKey, value: EncryptionContextValue }
                    @aws.polymorph#dafnyUtf8Bytes string EncryptionContextKey
                    @aws.polymorph#dafnyUtf8Bytes string EncryptionContextValue
                    """.formatted(SERVICE_NAMESPACE));
        });
        final Map<Path, TokenTree> codeByPath = codegen.generate();
        final String actualCode = codeByPath.get(Path.of("FoobarServiceFactory.dfy")).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                include "../StandardLibrary/StandardLibrary.dfy"
                include "../Util/UTF8.dfy"
                module {:extern "Dafny.Test.Foobar"} Test.Foobar {
                    import opened Wrappers
                    import opened StandardLibrary.UInt
                    import opened UTF8
                    type EncryptionContextKey = ValidUTF8Bytes
                    type EncryptionContextType = map<EncryptionContextKey, EncryptionContextValue>
                    type EncryptionContextValue = ValidUTF8Bytes
                    trait IFoobarServiceFactoryClient {
                        predicate {:opaque} DoItCalledWith() {true}
                        predicate {:opaque} DoItSucceededWith() {true}
                        method DoIt() returns (output: Result<(), FoobarServiceFactoryError>)
                           ensures DoItCalledWith()
                           ensures output.Success? ==> DoItSucceededWith()
                    }
                    trait FoobarServiceFactoryError {
                        function method GetMessage(): (message: string)
                            reads this
                    }
                    class UnknownFoobarServiceFactoryError extends FoobarServiceFactoryError {
                        var message: string
                        constructor(message: string) {
                            this.message := message;
                        }
                        function method GetMessage(): (message: string)
                            reads this
                        {
                            this.message
                        }
                    }
                    type SomeBool = bool
                    datatype SomeEnum = | A | B
                    type SomeList = seq<string>
                    type SomeLong = int64
                    datatype SomeStructure = SomeStructure(nameonly someInt: Option<int32>)
                }
                """);
        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateBlobTypeDefinition() {
        final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) -> modelAssembler.addUnparsedModel("test.smithy", """
                namespace %s
                @length(min: 1, max: 1024)
                blob SomeBlob
                """.formatted(SERVICE_NAMESPACE)));
        final String actualCode = codegen.generateBlobTypeDefinition(
                ShapeId.fromParts(SERVICE_NAMESPACE, "SomeBlob")).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                type SomeBlob = x: seq<uint8> | IsValid_SomeBlob(x) witness *
                predicate method IsValid_SomeBlob(x: seq<uint8>) { (1 <= |x| <= 1024) }
                """);
        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateBoolTypeDefinition() {
        final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) -> modelAssembler.addUnparsedModel("test.smithy", """
                namespace %s
                boolean SomeBool
                """.formatted(SERVICE_NAMESPACE)));
        final String actualCode = codegen.generateBoolTypeDefinition(
                ShapeId.fromParts(SERVICE_NAMESPACE, "SomeBool")).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("type SomeBool = bool");
        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateStringTypeDefinition() {
        final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) -> modelAssembler.addUnparsedModel("test.smithy", """
                namespace %s
                @length(min: 1, max: 1024)
                string SomeString
                """.formatted(SERVICE_NAMESPACE)));
        final String actualCode = codegen.generateStringTypeDefinition(
                ShapeId.fromParts(SERVICE_NAMESPACE, "SomeString")).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                type SomeString = x: string | IsValid_SomeString(x) witness *
                predicate method IsValid_SomeString(x: string) { (1 <= |x| <= 1024) }
                """);
        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateEnumTypeDefinition() {
        final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) ->
                modelAssembler.addUnparsedModel("test.smithy", """
                        namespace %s
                        @enum([
                            {value: "V1", name: "N1"},
                            {value: "V2", name: "N2"},
                            {value: "V3", name: "N3"},
                        ])
                        string SomeEnum
                        """.formatted(SERVICE_NAMESPACE)));
        final String actualCode = codegen.generateEnumTypeDefinition(
                ShapeId.fromParts(SERVICE_NAMESPACE, "SomeEnum")).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("datatype SomeEnum = | N1 | N2 | N3");
        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateNumericTypeDefinitionInt() {
        final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) -> modelAssembler.addUnparsedModel("test.smithy", """
                namespace %s
                @range(min: 1, max: 10)
                integer SomeInt
                """.formatted(SERVICE_NAMESPACE)));

        final String actualCode = codegen.generateNumericTypeDefinition(
                ShapeId.fromParts(SERVICE_NAMESPACE, "SomeInt")).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                type SomeInt = x: int32 | IsValid_SomeInt(x) witness *
                predicate method IsValid_SomeInt(x: int32) { (1 <= x <= 10) }
                """);
        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateNumericTypeDefinitionLong() {
        final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) -> modelAssembler.addUnparsedModel("test.smithy", """
                namespace %s
                @range(min: 1, max: 10)
                long SomeLong
                """.formatted(SERVICE_NAMESPACE)));

        final String actualCode = codegen.generateNumericTypeDefinition(
                ShapeId.fromParts(SERVICE_NAMESPACE, "SomeLong")).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                type SomeLong = x: int64 | IsValid_SomeLong(x) witness *
                predicate method IsValid_SomeLong(x: int64) { (1 <= x <= 10) }
                """);
        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateListTypeDefinition() {
        final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) -> modelAssembler.addUnparsedModel("test.smithy", """
                namespace %s
                @length(min: 1, max: 10)
                list SomeList {
                    member: Boolean
                }
                """.formatted(SERVICE_NAMESPACE)));
        final String actualCode = codegen.generateListTypeDefinition(
                ShapeId.fromParts(SERVICE_NAMESPACE, "SomeList")).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                type SomeList = x: seq<bool> | IsValid_SomeList(x) witness *
                predicate method IsValid_SomeList(x: seq<bool>) { (1 <= |x| <= 10) }
                """);
        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateMapTypeDefinition() {
        final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) -> modelAssembler.addUnparsedModel("test.smithy", """
                namespace %s
                @length(min: 1, max: 10)
                map SomeMap {
                    key: String,
                    value: Boolean,
                }
                """.formatted(SERVICE_NAMESPACE)));
        final String actualCode = codegen.generateMapTypeDefinition(
                ShapeId.fromParts(SERVICE_NAMESPACE, "SomeMap")).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                type SomeMap = x: map<string, bool> | IsValid_SomeMap(x) witness *
                predicate method IsValid_SomeMap(x: map<string, bool>) { (1 <= |x| <= 10) }
                """);
        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateStructureTypeDefinition() {
        final StructureShape foobarStructureShape = TestModel.setupFoobarStructureShape();
        final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) -> modelAssembler.addShape(foobarStructureShape));

        final String actualCode = codegen.generateStructureTypeDefinition(foobarStructureShape.getId()).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                datatype Foobar = Foobar(
                    nameonly someInt: Option<int32>,
                    nameonly someString: Option<string>,
                    nameonly someBool: bool
                )
                """);
        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateServiceTraitDefinition() {
        final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) -> {
            builder.addOperation(ShapeId.fromParts(SERVICE_NAMESPACE, "DoThis"));
            builder.addOperation(ShapeId.fromParts(SERVICE_NAMESPACE, "DoThat"));
            modelAssembler.addUnparsedModel("test.smithy", """
                    namespace %s
                    operation DoThis {}
                    operation DoThat {}
                    """.formatted(SERVICE_NAMESPACE));
        });
        final String actualCode = codegen.generateServiceTraitDefinition().toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                trait IFoobarServiceFactoryClient {
                    predicate {:opaque} DoThisCalledWith() {true}
                    predicate {:opaque} DoThisSucceededWith() {true}
                    method DoThis() returns (output: Result<(), FoobarServiceFactoryError>)
                      ensures DoThisCalledWith()
                      ensures output.Success? ==> DoThisSucceededWith()
                    predicate {:opaque} DoThatCalledWith() {true}
                    predicate {:opaque} DoThatSucceededWith() {true}
                    method DoThat() returns (output: Result<(), FoobarServiceFactoryError>)
                      ensures DoThatCalledWith()
                      ensures output.Success? ==> DoThatSucceededWith()
                }""");
        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateOperationPredicatesAndMethod() {
        final ShapeId operationShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "DoIt");
        final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) -> {
            builder.addOperation(operationShapeId);
            modelAssembler.addUnparsedModel("test.smithy", """
                    namespace %s
                    operation DoIt { input: Foo, output: Bar, errors: [Oops] }
                    structure Foo {}
                    structure Bar {}
                    @error("client") structure Oops {}
                    """.formatted(SERVICE_NAMESPACE));
        });
        final String actualCode = codegen.generateOperationPredicatesAndMethod(operationShapeId).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                predicate {:opaque} DoItCalledWith(
                  input: Foo
                ) {true}
                predicate {:opaque} DoItSucceededWith(
                  input: Foo,
                  output: Bar
                ) {true}
                method DoIt(input: Foo) returns (output: Result<Bar, FoobarServiceFactoryError>)
                  ensures DoItCalledWith(input)
                  ensures output.Success? ==> DoItSucceededWith(input, output.value)
                """);
        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateServiceErrorTraitDefinition() {
        final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) -> {
            builder.addOperation(ShapeId.fromParts(SERVICE_NAMESPACE, "DoIt"));
            modelAssembler.addUnparsedModel("test.smithy", """
                    namespace %s
                    operation DoIt { errors: [Oops, OhNo, Whoops] }
                    @error("client") structure Oops {}
                    @error("client") structure OhNo {}
                    @error("server") structure Whoops {}
                    """.formatted(SERVICE_NAMESPACE));
        });
        final String actualCode = codegen.generateServiceErrorTraitDefinition().toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                trait FoobarServiceFactoryError {
                    function method GetMessage(): (message: string)
                        reads this
                }
                """);
        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateSpecificErrorClass() {
        final ShapeId shapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "OopsException");
        final DafnyApiCodegen codegen = setupCodegen((builder, modelAssembler) -> {
            builder.addOperation(ShapeId.fromParts(SERVICE_NAMESPACE, "DoIt"));
            modelAssembler.addUnparsedModel("test.smithy", """
                    namespace %s
                    string ErrorMessageType
                    operation DoIt { errors: [OopsException] }
                    @error("client") structure OopsException { message: ErrorMessageType }
                    """.formatted(SERVICE_NAMESPACE));
        });
        final String actualCode = codegen.generateSpecificErrorClass(codegen.getModel().expectShape(shapeId, StructureShape.class)).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);
        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                class OopsException extends FoobarServiceFactoryError {
                    var message: string
                    
                    constructor (message: string) {
                        this.message := message;
                    }
                    
                    function method GetMessage(): (message: string)
                        reads this
                    {
                        this.message
                    }
                }
                """);
        assertEquals(expectedTokens, actualTokens);
    }
}
