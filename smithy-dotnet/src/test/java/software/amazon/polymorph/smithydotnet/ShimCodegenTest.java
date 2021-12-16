// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import org.junit.Test;
import software.amazon.polymorph.traits.ClientConfigTrait;
import software.amazon.polymorph.smithydotnet.util.TestModel;
import software.amazon.polymorph.smithydotnet.util.Tokenizer;
import software.amazon.polymorph.smithydotnet.util.Tokenizer.ParseToken;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;

import java.nio.file.Path;
import java.util.List;
import java.util.Set;
import java.util.function.BiConsumer;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.junit.Assert.*;
import static software.amazon.polymorph.smithydotnet.util.TestModel.SERVICE_NAMESPACE;
import static software.amazon.polymorph.smithydotnet.util.TestModel.SERVICE_SHAPE_ID;

public class ShimCodegenTest {
    private static ShimCodegen setupCodegen(final BiConsumer<ServiceShape.Builder, ModelAssembler> updater) {
        final Model model = TestModel.setupModel(updater);
        return new ShimCodegen(model, SERVICE_SHAPE_ID);
    }

    @Test
    public void testGenerateAll() {
        final ShimCodegen codegen = setupCodegen((builder, modelAssembler) ->
                modelAssembler.addUnparsedModel("test.smithy", """
                        namespace %s
                        resource Thing {}
                        """.formatted(SERVICE_NAMESPACE)));

        final Set<Path> expectedPaths = Stream.of("FoobarServiceClient", "Thing")
                .map(name -> Path.of(name + ".cs")).collect(Collectors.toSet());
        final Set<Path> actualPaths = codegen.generate().keySet();
        assertEquals(expectedPaths, actualPaths);
    }

    @Test
    public void testGenerateServiceShim() {
        final ShapeId operationShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "DoIt");
        final ShimCodegen codegen = setupCodegen((builder, modelAssembler) -> {
            modelAssembler.addShape(OperationShape.builder().id(operationShapeId).build());
            builder.addOperation(operationShapeId);
        });

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                namespace Test.Foobar {
                    public class FoobarServiceClient : FoobarServiceClientBase {
                        private Dafny.Test.Foobar.FoobarServiceClient.FoobarServiceClient _impl;
                        public FoobarServiceClient() {
                            this._impl = new Dafny.Test.Foobar.FoobarServiceClient.FoobarServiceClient();
                        }
                        protected override void _DoIt() { this._impl.DoIt(); }
                    }
                }
                """);

        final String actualCode = codegen.generateServiceShim().toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateServiceConstructorWithConfig() {
        final ShapeId configShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Config");
        final ShimCodegen codegen = setupCodegen((builder, modelAssembler) -> {
            modelAssembler.addShape(StructureShape.builder().id(configShapeId).build());
            builder.addTrait(ClientConfigTrait.builder().clientConfigId(configShapeId).build());
        });

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                public FoobarServiceClient(Test.Foobar.Config config) : base(config) {
                    this._impl = new Dafny.Test.Foobar.FoobarServiceClient.FoobarServiceClient(%s(config));
                }
                """.formatted(DotNetNameResolver.qualifiedTypeConverter(configShapeId, TypeConversionDirection.TO_DAFNY)));

        final String actualCode = codegen.generateServiceConstructor().toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateServiceConstructorWithoutConfig() {
        final ShimCodegen codegen = setupCodegen((_builder, _modelAssembler) -> {});

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                public FoobarServiceClient() {
                    this._impl = new Dafny.Test.Foobar.FoobarServiceClient.FoobarServiceClient();
                }
                """);

        final String actualCode = codegen.generateServiceConstructor().toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateResourceShim() {
        final ShimCodegen codegen = setupCodegen((builder, modelAssembler) -> modelAssembler.addUnparsedModel("test.smithy", """
                    namespace %s
                    resource Doer { operations: [DoIt] }
                    operation DoIt {}
                    """.formatted(SERVICE_NAMESPACE)));
        final ShapeId resourceShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Doer");

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                namespace Test.Foobar {
                    internal class Doer : DoerBase {
                        internal Dafny.Test.Foobar.IDoer _impl { get; }
                        internal Doer(Dafny.Test.Foobar.IDoer impl) { this._impl = impl; }
                        protected override void _DoIt() { this._impl.DoIt(); }
                    }
                }
                """);

        final String actualCode = codegen.generateResourceShim(resourceShapeId).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateResourceConstructor() {
        final ShimCodegen codegen = setupCodegen((builder, modelAssembler) -> modelAssembler.addUnparsedModel("test.smithy", """
                    namespace %s
                    resource Thing {}
                    """.formatted(SERVICE_NAMESPACE)));
        final ShapeId resourceShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Thing");

        final List<ParseToken> expectedTokens = Tokenizer.tokenize(
                "internal Thing(Dafny.Test.Foobar.IThing impl) { this._impl = impl; }");

        final String actualCode = codegen.generateResourceConstructor(resourceShapeId).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateOperationShims() {
        final ShimCodegen codegen = setupCodegen((builder, modelAssembler) -> modelAssembler.addUnparsedModel("test.smithy", """
                    namespace %s
                    resource Doer { operations: [DoThis, DoThat] }
                    operation DoThis {}
                    operation DoThat {}
                    """.formatted(SERVICE_NAMESPACE)));
        final ShapeId resourceShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Doer");

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                protected override void _DoThis() { this._impl.DoThis(); }
                protected override void _DoThat() { this._impl.DoThat(); }
                """);

        final String actualCode = codegen.generateOperationShims(resourceShapeId).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateOperationShimInputOnly() {
        final ShimCodegen codegen = setupCodegen((builder, modelAssembler) -> modelAssembler.addUnparsedModel("test.smithy", """
                    namespace %s
                    operation DoIt { input: Input }
                    structure Input {}
                    """.formatted(SERVICE_NAMESPACE)));
        final ShapeId operationShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "DoIt");
        final ShapeId inputShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Input");

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                protected override void _DoIt(Test.Foobar.Input input) {
                    Dafny.Test.Foobar.Input internalInput = %s(input);
                    this._impl.DoIt(internalInput);
                }
                """.formatted(DotNetNameResolver.qualifiedTypeConverter(inputShapeId, TypeConversionDirection.TO_DAFNY)));

        final String actualCode = codegen.generateOperationShim(operationShapeId).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateOperationShimOutputOnly() {
        final ShimCodegen codegen = setupCodegen((builder, modelAssembler) -> modelAssembler.addUnparsedModel("test.smithy", """
                    namespace %s
                    operation DoIt { output: Output }
                    structure Output {}
                    """.formatted(SERVICE_NAMESPACE)));
        final ShapeId operationShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "DoIt");
        final ShapeId outputShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Output");

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                protected override Test.Foobar.Output _DoIt() {
                    Dafny.Test.Foobar.Output internalOutput =
                    this._impl.DoIt();
                    return %s(internalOutput);
                }
                """.formatted(DotNetNameResolver.qualifiedTypeConverter(outputShapeId, TypeConversionDirection.FROM_DAFNY)));

        final String actualCode = codegen.generateOperationShim(operationShapeId).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateOperationShimInputAndOutput() {
        final ShimCodegen codegen = setupCodegen((builder, modelAssembler) -> {
            modelAssembler.addUnparsedModel("test.smithy", """
                        namespace %s
                        operation DoIt { input: Input, output: Output }
                        structure Input {}
                        structure Output {}
                        """.formatted(SERVICE_NAMESPACE));
        });
        final ShapeId operationShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "DoIt");
        final ShapeId inputShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Input");
        final ShapeId outputShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Output");

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                protected override Test.Foobar.Output _DoIt(Test.Foobar.Input input) {
                    Dafny.Test.Foobar.Input internalInput = %s(input);
                    Dafny.Test.Foobar.Output internalOutput =
                    this._impl.DoIt(internalInput);
                    return %s(internalOutput);
                }
                """.formatted(
                        DotNetNameResolver.qualifiedTypeConverter(inputShapeId, TypeConversionDirection.TO_DAFNY),
                        DotNetNameResolver.qualifiedTypeConverter(outputShapeId, TypeConversionDirection.FROM_DAFNY)));

        final String actualCode = codegen.generateOperationShim(operationShapeId).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        assertEquals(expectedTokens, actualTokens);
    }
}
