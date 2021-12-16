// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import org.junit.Test;
import software.amazon.polymorph.traits.ClientConfigTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.polymorph.smithydotnet.util.TestModel;
import software.amazon.polymorph.smithydotnet.util.Tokenizer;
import software.amazon.polymorph.smithydotnet.util.Tokenizer.ParseToken;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.IntegerShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.EnumDefinition;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.Trait;
import software.amazon.smithy.model.traits.TraitDefinition;

import java.nio.file.Path;
import java.util.List;
import java.util.Objects;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertFalse;
import static org.junit.Assert.assertTrue;
import static software.amazon.polymorph.smithydotnet.util.TestModel.SERVICE_NAMESPACE;
import static software.amazon.polymorph.smithydotnet.util.TestModel.SERVICE_SHAPE_ID;

public class ServiceCodegenTest {
    @Test
    public void testGenerateEmptyService() {
        final Model model = TestModel.setupModel();
        final ServiceCodegen codegen = new ServiceCodegen(model, SERVICE_SHAPE_ID);
        final Path expectedPath = Path.of("IFoobarService.cs");
        final String actualCode = Objects.requireNonNull(codegen.generate().get(expectedPath)).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                namespace Test.Foobar {
                    public interface IFoobarService {
                    }
                }
                """);

        // Ignore the prelude
        final List<ParseToken> lastActualTokens = actualTokens.subList(
                actualTokens.size() - expectedTokens.size(), actualTokens.size());
        assertEquals(expectedTokens, lastActualTokens);
    }

    @Test
    public void testGenerateServiceClientBaseWithoutClientConfig() {
        final StructureShape inputShape = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingInput"))
                .build();
        final StructureShape outputShape = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingOutput"))
                .build();
        final OperationShape operationShape = OperationShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomething"))
                .input(inputShape.getId())
                .output(outputShape.getId())
                .build();
        final Model model = TestModel.setupModel((builder, modelAssembler) -> {
            modelAssembler.addShape(inputShape);
            modelAssembler.addShape(outputShape);
            builder.addOperation(operationShape.getId());
            modelAssembler.addShape(operationShape);
        });
        final ServiceCodegen codegen = new ServiceCodegen(model, SERVICE_SHAPE_ID);
        final ServiceShape serviceShape = model.expectShape(SERVICE_SHAPE_ID, ServiceShape.class);
        final String actualCode = codegen.generateServiceClientBase(serviceShape).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                namespace Test.Foobar {
                    public abstract class FoobarServiceClientBase : IFoobarService {
                        protected FoobarServiceClientBase() {}
                        
                        public Test.Foobar.DoSomethingOutput DoSomething(Test.Foobar.DoSomethingInput input) {
                            input.Validate();
                            return _DoSomething(input);
                        }
                        protected abstract Test.Foobar.DoSomethingOutput _DoSomething(
                            Test.Foobar.DoSomethingInput input);
                    }
                }
                """);

        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateServiceClientBaseWithClientConfig() {
        final StructureShape configShape = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "FoobarServiceClientConfig"))
                .build();
        final ClientConfigTrait configTrait = ClientConfigTrait.builder()
                .clientConfigId(configShape.getId())
                .build();
        final StructureShape inputShape = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingInput"))
                .build();
        final StructureShape outputShape = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingOutput"))
                .build();
        final OperationShape operationShape = OperationShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomething"))
                .input(inputShape.getId())
                .output(outputShape.getId())
                .build();
        final Model model = TestModel.setupModel((builder, modelAssembler) -> {
            modelAssembler.addShape(configShape);
            modelAssembler.addShape(inputShape);
            modelAssembler.addShape(outputShape);
            builder.addOperation(operationShape.getId());
            modelAssembler.addShape(operationShape);
            modelAssembler.addTrait(SERVICE_SHAPE_ID, configTrait);
        });
        final ServiceCodegen codegen = new ServiceCodegen(model, SERVICE_SHAPE_ID);
        final ServiceShape serviceShape = model.expectShape(SERVICE_SHAPE_ID, ServiceShape.class);
        final String actualCode = codegen.generateServiceClientBase(serviceShape).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);
        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                namespace Test.Foobar {
                    public abstract class FoobarServiceClientBase : IFoobarService {
                        public Test.Foobar.FoobarServiceClientConfig Config { get ; private set; }

                        protected FoobarServiceClientBase(Test.Foobar.FoobarServiceClientConfig Config) {
                            this.Config = Config;
                        }
                        
                        public Test.Foobar.DoSomethingOutput DoSomething(Test.Foobar.DoSomethingInput input) {
                            input.Validate();
                            return _DoSomething(input);
                        }
                        protected abstract Test.Foobar.DoSomethingOutput _DoSomething(
                            Test.Foobar.DoSomethingInput input);
                    }
                }
                """);

        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateServiceInterfaceMethod() {
        final StructureShape inputShape = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingInput"))
                .build();
        final StructureShape outputShape = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingOutput"))
                .build();
        final OperationShape operationShape = OperationShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomething"))
                .input(inputShape.getId())
                .output(outputShape.getId())
                .build();
        final Model model = TestModel.setupModel((builder, modelAssembler) -> {
            modelAssembler.addShape(inputShape);
            modelAssembler.addShape(outputShape);
            builder.addOperation(operationShape.getId());
            modelAssembler.addShape(operationShape);
        });
        final ServiceCodegen codegen = new ServiceCodegen(model, SERVICE_SHAPE_ID);
        final String actualCode = codegen.generateInterfaceMethod(operationShape.getId()).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                Test.Foobar.DoSomethingOutput DoSomething(Test.Foobar.DoSomethingInput input);
                """);

        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateServiceInterface() {
        final StructureShape inputShape = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingInput"))
                .build();
        final StructureShape outputShape = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingOutput"))
                .build();
        final OperationShape operationShape = OperationShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomething"))
                .input(inputShape.getId())
                .output(outputShape.getId())
                .build();
        final StructureShape inputShape2 = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingInput2"))
                .build();
        final StructureShape outputShape2 = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingOutput2"))
                .build();
        final OperationShape operationShape2 = OperationShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomething2"))
                .input(inputShape2.getId())
                .output(outputShape2.getId())
                .build();
        final Model model = TestModel.setupModel((builder, modelAssembler) -> {
            modelAssembler.addShape(inputShape);
            modelAssembler.addShape(outputShape);
            builder.addOperation(operationShape.getId());
            modelAssembler.addShape(operationShape);

            modelAssembler.addShape(inputShape2);
            modelAssembler.addShape(outputShape2);
            builder.addOperation(operationShape2.getId());
            modelAssembler.addShape(operationShape2);
        });
        final ServiceCodegen codegen = new ServiceCodegen(model, SERVICE_SHAPE_ID);
        final String actualCode = codegen.generateServiceInterface().toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                namespace Test.Foobar {
                    public interface IFoobarService {
                        Test.Foobar.DoSomethingOutput  DoSomething (Test.Foobar.DoSomethingInput  input);
                        Test.Foobar.DoSomethingOutput2 DoSomething2(Test.Foobar.DoSomethingInput2 input);
                    }
                }
                """);

        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateStructureClass() {
        final Model model = TestModel.setupModel((builder, modelAssembler) -> modelAssembler.addUnparsedModel("test.smithy", """
                namespace %s
                structure Foobar {
                    SomeBool: Boolean,
                    @required
                    SomeInt: Integer,
                    SomeString: String,
                }
                """.formatted(SERVICE_NAMESPACE)));

        final ServiceCodegen codegen = new ServiceCodegen(model, SERVICE_SHAPE_ID);
        final ShapeId shapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Foobar");
        final StructureShape structureShape = model.expectShape(shapeId, StructureShape.class);
        final String actualCode = codegen.generateStructureClass(structureShape).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                namespace Test.Foobar {
                    public class Foobar {
                        private bool? _someBool;
                        private int? _someInt;
                        private string _someString;
                        
                        public bool SomeBool {
                            get { return this._someBool.GetValueOrDefault(); }
                            set { this._someBool = value; }
                        }
                        public int SomeInt {
                            get { return this._someInt.GetValueOrDefault(); }
                            set { this._someInt = value; }
                        }
                        public string SomeString {
                            get { return this._someString; }
                            set { this._someString = value; }
                        }
                        
                        public void Validate() {
                        }
                    }
                }
                """);

        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateResourceInterface() {
        // Input, no output
        final StructureShape inputShape = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingInput"))
                .build();
        final OperationShape operationInputShape = OperationShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingWithInput"))
                .input(inputShape.getId())
                .build();

        // Output, no input
        final StructureShape outputShape = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingOutput"))
                .build();
        final OperationShape operationOutputShape = OperationShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingWithOutput"))
                .output(outputShape.getId())
                .build();

        final ResourceShape resourceShape = ResourceShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "Baz"))
                .addOperation(operationInputShape)
                .addOperation(operationOutputShape)
                .build();

        final Model model = TestModel.setupModel((builder, modelAssembler) -> {
            modelAssembler.addShape(inputShape);
            modelAssembler.addShape(outputShape);
            modelAssembler.addShape(operationInputShape);
            modelAssembler.addShape(operationOutputShape);
            modelAssembler.addShape(resourceShape);
        });

        final ServiceCodegen codegen = new ServiceCodegen(model, SERVICE_SHAPE_ID);
        final String actualCode = codegen.generateResourceInterface(resourceShape.getId()).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);
        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                namespace Test.Foobar {
                    public interface IBaz {
                        void DoSomethingWithInput(Test.Foobar.DoSomethingInput input);
                        Test.Foobar.DoSomethingOutput DoSomethingWithOutput();
                    }
                }
                """);

        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateResourceClass() {
        // Input, no output
        final StructureShape inputShape = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingInput"))
                .build();
        final OperationShape operationInputShape = OperationShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingWithInput"))
                .input(inputShape.getId())
                .build();

        // Output, no input
        final StructureShape outputShape = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingOutput"))
                .build();
        final OperationShape operationOutputShape = OperationShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingWithOutput"))
                .output(outputShape.getId())
                .build();

        final ResourceShape resourceShape = ResourceShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "Baz"))
                .addOperation(operationInputShape)
                .addOperation(operationOutputShape)
                .build();

        final Model model = TestModel.setupModel((builder, modelAssembler) -> {
            modelAssembler.addShape(inputShape);
            modelAssembler.addShape(outputShape);
            modelAssembler.addShape(operationInputShape);
            modelAssembler.addShape(operationOutputShape);
            modelAssembler.addShape(resourceShape);
        });

        final ServiceCodegen codegen = new ServiceCodegen(model, SERVICE_SHAPE_ID);
        final String actualCode = codegen.generateResourceClass(resourceShape.getId()).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);
        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                namespace Test.Foobar {
                    public abstract class BazBase : IBaz {
                        public void DoSomethingWithInput(Test.Foobar.DoSomethingInput input) {
                           input.Validate();
                           _DoSomethingWithInput(input);
                        }
                        protected abstract void _DoSomethingWithInput(Test.Foobar.DoSomethingInput input);
                        
                        public Test.Foobar.DoSomethingOutput DoSomethingWithOutput() {
                           return _DoSomethingWithOutput();
                        }
                        protected abstract Test.Foobar.DoSomethingOutput _DoSomethingWithOutput();
                    }
                }
                """);

        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateResourceClassWithPositionalOutput() {
        /*
         * Test that shapes marked with @positional are unwrapped to their single member shape rather than the wrapper
         * shape.
         */
        final StructureShape targetShape = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "TargetShape"))
                .build();
        final StructureShape wrapperShape = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "WrapperShape"))
                .addMember("baz", targetShape.getId())
                .addTrait(PositionalTrait.builder().build())
                .build();
        final OperationShape operationOutputShape = OperationShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingWithOutput"))
                .output(wrapperShape.getId())
                .build();

        final ResourceShape resourceShape = ResourceShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "Baz"))
                .addOperation(operationOutputShape)
                .build();

        final Model model = TestModel.setupModel((builder, modelAssembler) -> {
            modelAssembler.addShape(targetShape);
            modelAssembler.addShape(wrapperShape);
            modelAssembler.addShape(operationOutputShape);
            modelAssembler.addShape(resourceShape);
        });

        final ServiceCodegen codegen = new ServiceCodegen(model, SERVICE_SHAPE_ID);
        final String actualCode = codegen.generateResourceClass(resourceShape.getId()).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);
        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                namespace Test.Foobar {
                    public abstract class BazBase : IBaz {
                        public Test.Foobar.TargetShape DoSomethingWithOutput() {
                           return _DoSomethingWithOutput();
                        }
                        protected abstract Test.Foobar.TargetShape _DoSomethingWithOutput();
                    }
                }
                """);

        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testBadPositionalTrait() {
        /*
         * Test that a shape marked with @positional that has two members throws an exception
         */
        final StructureShape targetShape1 = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "TargetShape1"))
                .build();
        final StructureShape targetShape2 = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "TargetShape2"))
                .build();
        final StructureShape wrapperShape = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "WrapperShape"))
                .addMember("baz", targetShape1.getId())
                .addMember("bar", targetShape2.getId())
                .addTrait(PositionalTrait.builder().build())
                .build();
        final OperationShape operationOutputShape = OperationShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingWithOutput"))
                .output(wrapperShape.getId())
                .build();

        final ResourceShape resourceShape = ResourceShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "Baz"))
                .addOperation(operationOutputShape)
                .build();

        final Model model = TestModel.setupModel((builder, modelAssembler) -> {
            modelAssembler.addShape(targetShape1);
            modelAssembler.addShape(targetShape2);
            modelAssembler.addShape(wrapperShape);
            modelAssembler.addShape(operationOutputShape);
            modelAssembler.addShape(resourceShape);
        });

        final ServiceCodegen codegen = new ServiceCodegen(model, SERVICE_SHAPE_ID);
        try {
            codegen.generateResourceClass(resourceShape.getId()).toString();
        } catch (IllegalStateException e) {
            assertEquals(e.getMessage(), "Structures marked with '@positional' must have exactly one member");
        }
    }

    @Test
    public void testGenerateStructureWithReference() {
        /*
         * Tests that structures which contain members which are marked with @reference correctly use the referenced
         * service/resource rather than the wrapper.
         */
        final Model model = TestModel.setupModel((builder, modelAssembler) -> {
            modelAssembler.addUnparsedModel("test.smithy", """
                    namespace %s
                    use aws.polymorph#reference
                    resource Dummy {}
                    @reference(resource: Dummy) structure DummyReference {}
                    structure Container { dummy: DummyReference }
                    """.formatted(SERVICE_NAMESPACE));
        });

        final ServiceCodegen codegen = new ServiceCodegen(model, SERVICE_SHAPE_ID);
        final ShapeId memberId = ShapeId.fromParts(SERVICE_NAMESPACE, "Container", "dummy");
        final MemberShape memberShape = model.expectShape(memberId, MemberShape.class);
        final String actualCode = codegen.generateStructureClassField(memberShape).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

        final List<ParseToken> expectedTokens = Tokenizer.tokenize("private Test.Foobar.IDummy _dummy;");
        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateNamedEnumClass() {
        final EnumTrait enumTrait = EnumTrait.builder()
                .addEnum(EnumDefinition.builder()
                        .value("t2.nano")
                        .name("T2_NANO")
                        .documentation("t2.nano documentation")
                        .tags(List.of("ebsOnly"))
                        .build())
                .addEnum(EnumDefinition.builder()
                        .value("t2.micro")
                        .name("T2_MICRO")
                        .documentation("t2.micro documentation")
                        .tags(List.of("ebsOnly"))
                        .build())
                .addEnum(EnumDefinition.builder()
                        .value("m256.mega")
                        .name("M256_MEGA")
                        .deprecated(true)
                        .build())
                .build();
        final StringShape instanceTypeShape = StringShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "InstanceType"))
                .addTrait(enumTrait)
                .build();
        final Model model = TestModel.setupModel((builder, modelAssembler) -> modelAssembler.addShape(instanceTypeShape));

        final ServiceCodegen codegen = new ServiceCodegen(model, SERVICE_SHAPE_ID);
        final String actualCode = codegen.generateEnumClass(instanceTypeShape.getId()).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);
        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                namespace Test.Foobar {
                    using Amazon.Runtime;
                
                    public class InstanceType : ConstantClass {
                        /// <summary>
                        /// t2.nano documentation
                        /// </summary>
                        public static readonly InstanceType T2_NANO = new InstanceType("t2.nano");
                        
                        /// <summary>
                        /// t2.micro documentation
                        /// </summary>
                        public static readonly InstanceType T2_MICRO = new InstanceType("t2.micro");
                        
                        [System.Obsolete]
                        public static readonly InstanceType M256_MEGA = new InstanceType("m256.mega");
                        
                        public static readonly InstanceType[] Values = {M256_MEGA, T2_MICRO, T2_NANO};

                        public InstanceType(string value) : base(value) {}
                    }
                }
                """);

        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testGenerateUnnamedEnumClass() {
        final EnumTrait enumTrait = EnumTrait.builder()
                .addEnum(EnumDefinition.builder().value("t2.nano").build())
                .addEnum(EnumDefinition.builder().value("t2.micro").build())
                .build();
        final StringShape instanceTypeShape = StringShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "InstanceType"))
                .addTrait(enumTrait)
                .build();
        final Model model = TestModel.setupModel((builder, modelAssembler) -> modelAssembler.addShape(instanceTypeShape));

        final ServiceCodegen codegen = new ServiceCodegen(model, SERVICE_SHAPE_ID);
        final String actualCode = codegen.generateEnumClass(instanceTypeShape.getId()).toString();
        final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);
        final List<ParseToken> expectedTokens = Tokenizer.tokenize("""
                namespace Test.Foobar {
                    public class InstanceType {
                        public static readonly string[] Values = {"t2.micro", "t2.nano"};

                        public InstanceType(string value) : base(value) {}
                    }
                }
                """);

        assertEquals(expectedTokens, actualTokens);
    }

    @Test
    public void testShouldNotGenerateStructureReference() {
        final ReferenceTrait trait = ReferenceTrait.builder()
                .referentId(SERVICE_SHAPE_ID)
                .referentType(ReferenceTrait.ReferentType.RESOURCE)
                .build();
        final StructureShape foobarStructureShape = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "Foobar"))
                .addTrait(trait)
                .build();

        final Model model = TestModel.setupModel((builder, modelAssembler) -> modelAssembler.addShape(foobarStructureShape));
        final ServiceCodegen codegen = new ServiceCodegen(model, SERVICE_SHAPE_ID);

        assertFalse(
            "Should not try to generate class for structure marked with @reference",
            codegen.shouldGenerateStructure(foobarStructureShape)
        );
    }

    @Test
    public void testShouldNotGenerateStructurePositional() {
        final PositionalTrait trait = PositionalTrait.builder().build();
        final StructureShape foobarStructureShape = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "Foobar"))
                .addTrait(trait)
                .build();

        final Model model = TestModel.setupModel((builder, modelAssembler) -> modelAssembler.addShape(foobarStructureShape));
        final ServiceCodegen codegen = new ServiceCodegen(model, SERVICE_SHAPE_ID);

        assertFalse(
                "Should not try to generate class for structure marked with @positional",
                codegen.shouldGenerateStructure(foobarStructureShape)
        );
    }

    @Test
    public void testShouldNotGenerateStructureTrait() {
        final TraitDefinition trait = TraitDefinition.builder().build();
        final StructureShape foobarStructureShape = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "Foobar"))
                .addTrait(trait)
                .build();

        final Model model = TestModel.setupModel((builder, modelAssembler) -> modelAssembler.addShape(foobarStructureShape));
        final ServiceCodegen codegen = new ServiceCodegen(model, SERVICE_SHAPE_ID);

        assertFalse(
                "Should not try to generate class for structure marked with @trait",
                codegen.shouldGenerateStructure(foobarStructureShape)
        );
    }

    @Test
    public void testShouldGenerateStructureTrue() {
        final TraitDefinition trait = TraitDefinition.builder().build();
        final StructureShape foobarStructureShape = StructureShape.builder()
                .id(ShapeId.fromParts(SERVICE_NAMESPACE, "Foobar"))
                .build();

        final Model model = TestModel.setupModel((builder, modelAssembler) -> modelAssembler.addShape(foobarStructureShape));
        final ServiceCodegen codegen = new ServiceCodegen(model, SERVICE_SHAPE_ID);

        assertTrue(
                "Should have generated class for structure",
                codegen.shouldGenerateStructure(foobarStructureShape)
        );
    }

}
