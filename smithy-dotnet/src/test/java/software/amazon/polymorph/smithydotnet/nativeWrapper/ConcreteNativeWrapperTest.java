// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet.nativeWrapper;

import org.junit.Before;
import org.junit.Test;

import java.util.List;

import software.amazon.polymorph.smithydotnet.NativeWrapperCodegenTest;
import software.amazon.polymorph.util.TestModel;
import software.amazon.polymorph.util.Tokenizer;
import software.amazon.polymorph.util.Tokenizer.ParseToken;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ShapeId;

import static org.junit.Assert.assertEquals;
import static software.amazon.polymorph.util.TestModel.SERVICE_NAMESPACE;
import static software.amazon.polymorph.util.TestModel.SERVICE_SHAPE_ID;

public class ConcreteNativeWrapperTest extends NativeWrapperCodegenTest {

    protected ConcreteNativeWrapper underTest;

    @Before
    @Override
    public void setup(){
        super.setup();

        this.underTest = new ConcreteNativeWrapper(
                this.model,
                SERVICE_SHAPE_ID,
                ShapeId.fromParts(SERVICE_NAMESPACE, "Baz"),
                this.nameResolver);
    }

    @Test
    public void testGenerateCatchGeneralException() {
        final String dafnyOutput =
                """
                Wrappers_Compile.Result<
                  Dafny.Test.Foobar._IDoSomethingOutput,
                  Dafny.Test.Foobar.IFoobarServiceException
                >""";
        final String actual = this.underTest
                .generateCatchGeneralException(dafnyOutput)
                .toString();
        final String expected = ConcreteNativeWrapperTestConstants.CATCH_GENERAL_DO_OUTPUT;
        parseAndAssert(actual, expected);
    }

    @Test
    public void testGenerateCatchServiceException() {
        final String dafnyOutput =
                """
                Wrappers_Compile.Result<
                    Dafny.Test.Foobar._IDoSomethingOutput,
                    Dafny.Test.Foobar.IFoobarServiceException
                >""";
        final String actual = this.underTest
                .generateCatchServiceException(dafnyOutput)
                .toString();
        final String expected = ConcreteNativeWrapperTestConstants.CATCH_SERVICE_DO_OUTPUT;
        parseAndAssert(actual, expected);
    }

    @Test
    public void testGenerateOperationWrapperWithOutput() {
        String rawModel = """
                namespace test.foobar
                resource Baz { operations: [DoSomethingWithOutput] }
                operation DoSomethingWithOutput { output: DoSomethingOutput }
                structure DoSomethingOutput {}
                """;
        ConcreteNativeWrapper localUnderTest = setupLocalModel(rawModel);
        final String actual = localUnderTest.generateOperationWrapper(
                ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingWithOutput")
        ).toString();
        final String expected = ConcreteNativeWrapperTestConstants.DO_OUTPUT;
        parseAndAssert(actual, expected);
    }

    @Test
    public void testGenerateOperationWrapperWithInput() {
        String rawModel = """
                namespace test.foobar
                resource Baz { operations: [DoSomethingWithInput] }
                operation DoSomethingWithInput { input: DoSomethingInput }
                structure DoSomethingInput {}
                """;
        ConcreteNativeWrapper localUnderTest = setupLocalModel(rawModel);
        final String actual = localUnderTest.generateOperationWrapper(
                ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingWithInput")
        ).toString();
        final String expected = ConcreteNativeWrapperTestConstants.DO_INPUT;
        parseAndAssert(actual, expected);
    }

    @Test
    public void testGenerateConstructor(){
        final String className = "NativeWrapper_Baz";
        final String actual = this.underTest.generateConstructor(className)
                .toString();
        final String expected = ConcreteNativeWrapperTestConstants.CONSTRUCTOR;
        parseAndAssert(actual, expected);
    }

    @Test
    public void testGenerateClassSimple(){
        String rawModel = """
                namespace test.foobar
                resource Baz {}
                """;
        ConcreteNativeWrapper localUnderTest = setupLocalModel(rawModel);
        final String actual = localUnderTest.generateClass().toString();
        final String expected = ConcreteNativeWrapperTestConstants.SIMPLE_CLASS;
        parseAndAssert(actual, expected);
    }

    @Test
    public void testGenerateClassVoid(){
        String rawModel = """
                namespace test.foobar
                resource Baz {operations: [Do]}
                operation Do {}
                """;
        ConcreteNativeWrapper localUnderTest = setupLocalModel(rawModel);
        final String actual = localUnderTest.generateClass().toString();
        final String expected = ConcreteNativeWrapperTestConstants.VOID_CLASS;
        parseAndAssert(actual, expected);
    }

    @Test
    public void testGenerateClassComplete(){
        final String actual = this.underTest.generateClass().toString();
        final String expected = ConcreteNativeWrapperTestConstants.COMPLETE_CLASS;
        parseAndAssert(actual, expected);
    }

    @Test
    public void testGenerateConcrete() {
        final String actual = this.underTest.generateConcrete().toString();
        final String expected = ConcreteNativeWrapperTestConstants.COMPLETE;
        parseAndAssert(actual, expected);
    }

    ConcreteNativeWrapper setupLocalModel(String rawModel) {
        Model localModel = TestModel.setupModel(
                (builder, modelAssembler) -> modelAssembler
                        .addUnparsedModel("test.smithy", rawModel));
        return new ConcreteNativeWrapper(
                localModel,
                SERVICE_SHAPE_ID,
                ShapeId.fromParts(SERVICE_NAMESPACE, "Baz"),
                getNameResolver(localModel, SERVICE_SHAPE_ID));
    }

    void parseAndAssert(String actual, String expected) {
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actual);
        final List<ParseToken> expectedTokens = Tokenizer.tokenize(expected);
        assertEquals(expectedTokens, actualTokens);
    }
}
