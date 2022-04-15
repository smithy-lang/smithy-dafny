package software.amazon.polymorph.smithydotnet.nativeWrapper;

import org.junit.Before;
import org.junit.Test;

import java.util.List;
import java.util.Set;

import software.amazon.polymorph.smithydotnet.NativeWrapperCodegenTest;
import software.amazon.polymorph.util.TestModel;
import software.amazon.polymorph.util.Tokenizer;
import software.amazon.polymorph.util.Tokenizer.ParseToken;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.EntityShape;
import software.amazon.smithy.model.shapes.ShapeId;

import static org.junit.Assert.assertEquals;
import static software.amazon.polymorph.util.TestModel.SERVICE_NAMESPACE;
import static software.amazon.polymorph.util.TestModel.SERVICE_SHAPE_ID;

public class ConcreateTest extends NativeWrapperCodegenTest {

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
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actual);
        final String expected = """
                public override Wrappers_Compile._IResult<
                    _System._ITuple0,
                    Dafny.Test.Foobar.IFoobarServiceException
                > DoSomethingWithInput(Dafny.Test.Foobar._IDoSomethingInput input)
                {
                    // ReSharper disable once RedundantNameQualifier
                    Test.Foobar.DoSomethingInput nativeInput =
                        TypeConversion.FromDafny_N4_test__N6_foobar__S16_DoSomethingInput(
                            input);
                    try
                    {
                        _impl.DoSomethingWithInput(nativeInput);
                        return Wrappers_Compile.Result<
                            _System._ITuple0,
                            Dafny.Test.Foobar.IFoobarServiceException
                        >.create_Success();
                    }
                    catch (FoobarServiceBaseException e)
                    {
                        return Wrappers_Compile.Result<
                            _System._ITuple0,
                            Dafny.Test.Foobar.IFoobarServiceException
                        >.create_Failure(
                            TypeConversion.ToDafny_CommonError_FoobarServiceBaseException(e)
                        );
                    }
                    catch (Exception e)
                    {
                        return Wrappers_Compile.Result<
                            _System._ITuple0,
                            Dafny.Test.Foobar.IFoobarServiceException
                        >.create_Failure(
                            TypeConversion.ToDafny_CommonError_FoobarServiceBaseException(
                                new FoobarServiceBaseException(e.Message))
                        );
                    }
                }
                """;
        final List<ParseToken> expectedTokens = Tokenizer.tokenize(expected);
        assertEquals(expectedTokens, actualTokens);
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
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actual);
        final String expected = """
                public override Wrappers_Compile._IResult<
                    Dafny.Test.Foobar._IDoSomethingOutput,
                    Dafny.Test.Foobar.IFoobarServiceException
                > DoSomethingWithOutput()
                {
                    try
                    {
                        // ReSharper disable once RedundantNameQualifier
                        Test.Foobar.DoSomethingOutput nativeOutput = _impl.DoSomethingWithOutput();
                        return Wrappers_Compile.Result<
                            Dafny.Test.Foobar._IDoSomethingOutput,
                            Dafny.Test.Foobar.IFoobarServiceException
                        >.create_Success(
                            TypeConversion.ToDafny_N4_test__N6_foobar__S17_DoSomethingOutput(
                                nativeOutput)
                        );
                    }
                    catch (FoobarServiceBaseException e)
                    {
                        return Wrappers_Compile.Result<
                            Dafny.Test.Foobar._IDoSomethingOutput,
                            Dafny.Test.Foobar.IFoobarServiceException
                        >.create_Failure(
                            TypeConversion.ToDafny_CommonError_FoobarServiceBaseException(e)
                        );
                    }
                    catch (Exception e)
                    {
                        return Wrappers_Compile.Result<
                            Dafny.Test.Foobar._IDoSomethingOutput,
                            Dafny.Test.Foobar.IFoobarServiceException
                        >.create_Failure(
                            TypeConversion.ToDafny_CommonError_FoobarServiceBaseException(
                                new FoobarServiceBaseException(e.Message))
                        );
                    }
                }
                """;
        final List<ParseToken> expectedTokens = Tokenizer.tokenize(expected);
        assertEquals(expectedTokens, actualTokens);
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
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actual);
        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                catch (FoobarServiceBaseException e)
                {
                    return Wrappers_Compile.Result<
                        Dafny.Test.Foobar._IDoSomethingOutput,
                        Dafny.Test.Foobar.IFoobarServiceException
                    >.create_Failure(
                        TypeConversion.ToDafny_CommonError_FoobarServiceBaseException(e)
                    );
                }
                """);
        assertEquals(expectedTokens, actualTokens);
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
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actual);
        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                catch (Exception e)
                {
                    return Wrappers_Compile.Result<
                        Dafny.Test.Foobar._IDoSomethingOutput,
                        Dafny.Test.Foobar.IFoobarServiceException
                    >.create_Failure(
                        TypeConversion.ToDafny_CommonError_FoobarServiceBaseException(
                            new FoobarServiceBaseException(e.Message))
                    );
                }
                """);
        assertEquals(expectedTokens, actualTokens);
    }
}
