// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import org.junit.Test;
import software.amazon.polymorph.util.TestModel;
import software.amazon.polymorph.util.Tokenizer;
import software.amazon.polymorph.util.Tokenizer.ParseToken;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;

import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiConsumer;

import static org.junit.Assert.assertEquals;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.FROM_DAFNY;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.TO_DAFNY;
import static software.amazon.polymorph.util.Tokenizer.tokenizeAndAssertEqual;

public class AwsSdkShimCodegenTest {
    private static final String SERVICE_NAMESPACE = "com.amazonaws.foobar";
    private static final String SERVICE_NAME = "FoobarService";
    private static final ShapeId SERVICE_SHAPE_ID = ShapeId.fromParts(SERVICE_NAMESPACE, SERVICE_NAME);

    private static AwsSdkShimCodegen setupCodegen(final BiConsumer<ServiceShape.Builder, ModelAssembler> updater) {
        final Model model = TestModel.setupModel((builder, assembler) -> {
            builder.id(SERVICE_SHAPE_ID);
            updater.accept(builder, assembler);
        });
        final ServiceShape serviceShape = model.expectShape(SERVICE_SHAPE_ID, ServiceShape.class);
        return new AwsSdkShimCodegen(model, serviceShape, new Path[0]);
    }
    //TODO: apply AwsSdkShimCodegen refactor to tests
    @Test
    public void testGenerateEmptyService() {
        final AwsSdkShimCodegen codegen = setupCodegen((_builder, _modelAssembler) -> {});
        final Map<Path, TokenTree> codeByPath = codegen.generate();
        final Path shimPath = Path.of("FoobarServiceShim.cs");
        assert codeByPath.keySet().equals(Set.of(shimPath));

        final String actual = codeByPath.get(shimPath).toString();

        final String stringConverter = AwsSdkDotNetNameResolver.qualifiedTypeConverter(
                ShapeId.from("smithy.api#String"), TO_DAFNY);
        final String expected = """
                using System;
                using System.IO;
                using System.Collections.Generic;
                
                namespace Com.Amazonaws.Foobar {
                    public class FoobarServiceShim : Dafny.Com.Amazonaws.Foobar.Types.IFoobarServiceClient {
                        public Amazon.FoobarService.AmazonFoobarServiceClient _impl;
                        
                        public FoobarServiceShim(Amazon.FoobarService.AmazonFoobarServiceClient impl) {
                            this._impl = impl;
                        }
                        
                        private Dafny.Com.Amazonaws.Foobar.Types._IError ConvertError(
                                Amazon.FoobarService.AmazonFoobarServiceException error) {
                            switch (error) {
                                default:
                                    return new Dafny.Com.Amazonaws.Foobar.Types.Error_Opaque(error);
                            }
                        }
                    }
                }
                """.formatted(stringConverter);

        tokenizeAndAssertEqual(actual, expected);
    }

    @Test
    public void testGenerateServiceShim() {
        final ShapeId inputOperation = ShapeId.fromParts(SERVICE_NAMESPACE, "DoInput");
        final ShapeId outputOperation = ShapeId.fromParts(SERVICE_NAMESPACE, "DoOutput");
        final AwsSdkShimCodegen codegen = setupCodegen((builder, modelAssembler) -> {
            builder.addOperation(inputOperation);
            builder.addOperation(outputOperation);
            modelAssembler.addUnparsedModel("test.smithy", """
                    namespace com.amazonaws.foobar
                    operation DoInput {
                        input: DoInputRequest,
                        errors: [Crash],
                    }
                    operation DoOutput {
                        output: DoOutputResponse,
                        errors: [Crash],
                    }
                    structure DoInputRequest {}
                    structure DoOutputResponse {}
                    @error("client") structure Crash { message: String }
                    """);
        });
        final List<ParseToken> actualTokens = Tokenizer.tokenize(codegen.generateServiceShim().toString());

        final String expectedShimConstructor = codegen.generateServiceShimConstructor().toString();
        final String expectedInputOperationShim = codegen.generateOperationShim(inputOperation).toString();
        final String expectedOutputOperationShim = codegen.generateOperationShim(outputOperation).toString();
        final String expectedErrorTypeShim = codegen.generateErrorTypeShim().toString();
        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                namespace Com.Amazonaws.Foobar {
                    public class FoobarServiceShim : Dafny.Com.Amazonaws.Foobar.Types.IFoobarServiceClient {
                        public Amazon.FoobarService.AmazonFoobarServiceClient _impl;
                        %s
                        %s
                        %s
                        %s
                    }
                }
                """.formatted(
                        expectedShimConstructor,
                        expectedInputOperationShim,
                        expectedOutputOperationShim,
                        expectedErrorTypeShim));

        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateOperationShim() {
        final ShapeId operationShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Go");
        final ShapeId requestShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "GoRequest");
        final ShapeId responseShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "GoResponse");
        final AwsSdkShimCodegen codegen = setupCodegen((builder, modelAssembler) -> {
            builder.addOperation(operationShapeId);
            modelAssembler.addUnparsedModel("test.smithy", """
                    namespace com.amazonaws.foobar
                    operation Go {
                        input: GoRequest,
                        output: GoResponse,
                        errors: [Crash],
                    }
                    structure GoRequest {}
                    structure GoResponse {}
                    @error("client") structure Crash { message: String }
                    """);
        });

        final List<ParseToken> actualTokens = Tokenizer.tokenize(
                codegen.generateOperationShim(operationShapeId).toString());

        final String resultTypeParams = "%s, %s".formatted(
                "Dafny.Com.Amazonaws.Foobar.Types._IGoResponse", "Dafny.Com.Amazonaws.Foobar.Types._IError");
        final String requestFromDafnyConverter =
                AwsSdkDotNetNameResolver.qualifiedTypeConverter(requestShapeId, FROM_DAFNY);
        final String responseToDafnyConverter =
                AwsSdkDotNetNameResolver.qualifiedTypeConverter(responseShapeId, TO_DAFNY);
        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                public Wrappers_Compile._IResult<%1$s> Go(Dafny.Com.Amazonaws.Foobar.Types._IGoRequest request) {
                    Amazon.FoobarService.Model.GoRequest sdkRequest = %2$s(request);
                    try {
                        Amazon.FoobarService.Model.GoResponse sdkResponse =
                            this._impl.GoAsync(sdkRequest).Result;
                        return Wrappers_Compile.Result<%1$s>.create_Success(%3$s(sdkResponse));
                    }
                    catch (System.AggregateException aggregate)
                        when (aggregate.InnerException is Amazon.FoobarService.AmazonFoobarServiceException ex) {
                        return Wrappers_Compile.Result<%1$s>.create_Failure(this.ConvertError(ex));
                    }
                }
                """.formatted(resultTypeParams, requestFromDafnyConverter, responseToDafnyConverter));

        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateErrorTypeShim() {
        final ShapeId operationShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Go");
        final AwsSdkShimCodegen codegen = setupCodegen((builder, modelAssembler) -> {
            builder.addOperation(operationShapeId);
            modelAssembler.addUnparsedModel("test.smithy", """
                    namespace com.amazonaws.foobar
                    operation Go {
                        errors: [Boom, Crash, Bang],
                    }
                    @error("client") structure Boom { message: String }
                    @error("client") structure Crash { message: String }
                    @error("client") structure Bang { message: String }
                    """);
        });
        final List<ParseToken> actualTokens = Tokenizer.tokenize(codegen.generateErrorTypeShim().toString());

        final String bangConverter = AwsSdkDotNetNameResolver.qualifiedTypeConverter(
                ShapeId.from("com.amazonaws.foobar#Bang"), TO_DAFNY);
        final String boomConverter = AwsSdkDotNetNameResolver.qualifiedTypeConverter(
                ShapeId.from("com.amazonaws.foobar#Boom"), TO_DAFNY);
        final String crashConverter = AwsSdkDotNetNameResolver.qualifiedTypeConverter(
                ShapeId.from("com.amazonaws.foobar#Crash"), TO_DAFNY);
        final String stringConverter = AwsSdkDotNetNameResolver.qualifiedTypeConverter(
                ShapeId.from("smithy.api#String"), TO_DAFNY);
        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                private Dafny.Com.Amazonaws.Foobar.Types._IError ConvertError(
                        Amazon.FoobarService.AmazonFoobarServiceException error) {
                    switch (error) {
                        case Amazon.FoobarService.Model.BangException e:
                            return %s(e);
                        case Amazon.FoobarService.Model.BoomException e:
                            return %s(e);
                        case Amazon.FoobarService.Model.CrashException e:
                            return %s(e);
                        default:
                            return new Dafny.Com.Amazonaws.Foobar.Types.Error_Opaque(error);
                    }
                }
                """.formatted(bangConverter, boomConverter, crashConverter, stringConverter));

        assertEquals(expectedTokens, actualTokens);
    }
}
