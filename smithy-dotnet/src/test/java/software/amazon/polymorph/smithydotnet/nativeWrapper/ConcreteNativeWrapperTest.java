// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet.nativeWrapper;

import org.junit.Before;
import org.junit.Test;

import java.util.List;
import java.util.Optional;

import software.amazon.polymorph.smithydotnet.NativeWrapperCodegenTest;
import software.amazon.polymorph.util.TestModel;
import software.amazon.polymorph.util.Tokenizer;
import software.amazon.polymorph.util.Tokenizer.ParseToken;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ShapeId;

import static org.junit.Assert.assertEquals;
import static software.amazon.polymorph.util.TestModel.SERVICE_NAMESPACE;
import static software.amazon.polymorph.util.TestModel.SERVICE_SHAPE_ID;

// Debugging Guidance: These tests are arranged from Simplest to Most Complete.
// Generally, the simplest unit test have shorter durations.
// As such, if you sort the failed unit tests by duration, you can find
// the simplest unit test that is failing.
// Addressing that unit test will often resolve the more complex failures.
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
    public void testGenerateValidateNativeOutput() {
        ShapeId outputShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingOutput");
        String nativeOutputType = "Test.Foobar.DoSomethingOutput";
        final String actual = this.underTest
                .generateValidateNativeOutputMethod(
                        Optional.of(outputShapeId),
                        Optional.of(nativeOutputType),
                        "DoSomethingWithOutput")
                .toString();
        final String expected = ConcreteNativeWrapperTestConstants.VALIDATE_NATIVE_OUTPUT
                .formatted(nativeOutputType, "DoSomethingWithOutput");
        parseAndAssert(actual, expected);
    }

    @Test
    public void testGenerateCatchServiceException() {
        final String actual = this.underTest.generateCatchServiceException().toString();
        final String expected = ConcreteNativeWrapperTestConstants.CATCH_SERVICE;
        parseAndAssert(actual, expected);
    }

    @Test
    public void testGenerateOperationWrapperWithOutput() {
        String rawModel = """
                namespace test.foobar
                use aws.polymorph#positional
                resource Baz { operations: [DoSomethingWithOutput] }
                operation DoSomethingWithOutput { output: DoSomethingOutput }
                structure DoSomethingOutput {}
                """;
        ConcreteNativeWrapper localUnderTest = setupLocalModel(rawModel);
        final String actual = localUnderTest.generateOperationWrapper(
                ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingWithOutput")
        ).toString();
        final String expected = ConcreteNativeWrapperTestConstants.DO_OUTPUT_NOT_POSITIONAL;
        parseAndAssert(actual, expected);
    }

    @Test
    public void testGenerateOperationWrapperWithOutputPositional() {
        String rawModel = """
                namespace test.foobar
                use aws.polymorph#positional
                use aws.polymorph#reference
                resource Thing {}
                @reference(resource: Thing)
                structure ThingReference {}
                resource Baz { operations: [DoSomethingWithOutput] }
                operation DoSomethingWithOutput { output: DoSomethingOutput }
                @positional
                structure DoSomethingOutput { thing: ThingReference }
                """;
        ConcreteNativeWrapper localUnderTest = setupLocalModel(rawModel);
        final String actual = localUnderTest.generateOperationWrapper(
                ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingWithOutput")
        ).toString();
        final String expected = ConcreteNativeWrapperTestConstants.DO_OUTPUT_POSITIONAL;
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
