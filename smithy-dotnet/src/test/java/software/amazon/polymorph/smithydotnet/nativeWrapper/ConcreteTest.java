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

public class ConcreteTest extends NativeWrapperCodegenTest {

    protected Concrete underTest;

    @Before
    @Override
    public void setup(){
        super.setup();
        this.underTest = new Concrete(
                this.model,
                SERVICE_SHAPE_ID,
                ShapeId.fromParts(SERVICE_NAMESPACE, "Baz"));
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
        final String expected = ConcreteTestConstants.CATCH_GENERAL_DO_OUTPUT;
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
        final String expected = ConcreteTestConstants.CATCH_SERVICE_DO_OUTPUT;
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
        Model localModel = TestModel.setupModel(
                (builder, modelAssembler) -> modelAssembler
                        .addUnparsedModel("test.smithy", rawModel));
        Concrete localUnderTest = new Concrete(
                localModel,
                SERVICE_SHAPE_ID,
                ShapeId.fromParts(SERVICE_NAMESPACE, "Baz"));
        final String actual = localUnderTest.generateOperationWrapper(
                ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingWithOutput")
        ).toString();
        final String expected = ConcreteTestConstants.DO_OUTPUT;
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
        Model localModel = TestModel.setupModel(
                (builder, modelAssembler) -> modelAssembler
                        .addUnparsedModel("test.smithy", rawModel));
        Concrete localUnderTest = new Concrete(
                localModel,
                SERVICE_SHAPE_ID,
                ShapeId.fromParts(SERVICE_NAMESPACE, "Baz"));
        final String actual = localUnderTest.generateOperationWrapper(
                ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingWithInput")
        ).toString();
        final String expected = ConcreteTestConstants.DO_INPUT;
        parseAndAssert(actual, expected);
    }

    @Test
    public void testGenerateConstructor(){
        final String className = "NativeWrapper_Baz";
        final String actual = this.underTest.generateConstructor(className)
                .toString();
        final String expected = ConcreteTestConstants.CONSTRUCTOR;
        parseAndAssert(actual, expected);
    }

    @Test
    public void testGenerateClassSimple(){
        String rawModel = """
                namespace test.foobar
                resource Baz {}
                """;
        Model localModel = TestModel.setupModel(
                (builder, modelAssembler) -> modelAssembler
                        .addUnparsedModel("test.smithy", rawModel));
        Concrete localUnderTest = new Concrete(
                localModel,
                SERVICE_SHAPE_ID,
                ShapeId.fromParts(SERVICE_NAMESPACE, "Baz"));
        final String actual = localUnderTest.generateClass().toString();
        final String expected = ConcreteTestConstants.SIMPLE_CLASS;
        parseAndAssert(actual, expected);
    }

    @Test
    public void testGenerateClassVoid(){
        String rawModel = """
                namespace test.foobar
                resource Baz {operations: [Do]}
                operation Do {}
                """;
        Model localModel = TestModel.setupModel(
                (builder, modelAssembler) -> modelAssembler
                        .addUnparsedModel("test.smithy", rawModel));
        Concrete localUnderTest = new Concrete(
                localModel,
                SERVICE_SHAPE_ID,
                ShapeId.fromParts(SERVICE_NAMESPACE, "Baz"));
        final String actual = localUnderTest.generateClass().toString();
        final String expected = ConcreteTestConstants.VOID_CLASS;
        parseAndAssert(actual, expected);
    }

    @Test
    public void testGenerateClassComplete(){
        final String actual = this.underTest.generateClass().toString();
        final String expected = ConcreteTestConstants.COMPLETE_CLASS;
        parseAndAssert(actual, expected);
    }

    @Test
    public void testGenerateConcrete() {
        final String actual = this.underTest.generateConcrete().toString();
        final String expected = ConcreteTestConstants.COMPLETE;
        parseAndAssert(actual, expected);
    }

    void parseAndAssert(String actual, String expected) {
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actual);
        final List<ParseToken> expectedTokens = Tokenizer.tokenize(expected);
        assertEquals(expectedTokens, actualTokens);
    }
}
