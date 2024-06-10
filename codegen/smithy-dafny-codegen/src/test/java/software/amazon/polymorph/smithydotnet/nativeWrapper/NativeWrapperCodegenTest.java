// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet.nativeWrapper;

import static software.amazon.polymorph.util.TestModel.SERVICE_NAMESPACE;
import static software.amazon.polymorph.util.TestModel.SERVICE_SHAPE_ID;
import static software.amazon.polymorph.util.Tokenizer.tokenizeAndAssertEqual;

import java.util.Optional;
import org.junit.Before;
import org.junit.Test;
import software.amazon.polymorph.smithydotnet.DotNetNameResolver;
import software.amazon.polymorph.util.TestModel;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;

// Debugging Guidance:
// These tests are arranged from Simplest to Most Complete.
// Generally, the simplest unit test have shorter durations.
// As such, if you sort the failed unit tests by duration,
// you can find the simplest unit test that is failing.
// Addressing that unit test will often resolve the more complex failures.
public class NativeWrapperCodegenTest {

  protected Model model;
  protected DotNetNameResolver nameResolver;
  protected NativeWrapperCodegen underTest;

  @Before
  public void setup() {
    String rawModel =
      """
      namespace test.foobar
      resource Baz { operations: [DoSomethingWithInput, DoSomethingWithOutput] }
      operation DoSomethingWithInput { input: DoSomethingInput }
      structure DoSomethingInput {}
      operation DoSomethingWithOutput { output: DoSomethingOutput }
      structure DoSomethingOutput {}
      """;

    this.model =
      TestModel.setupModel((builder, modelAssembler) ->
        modelAssembler.addUnparsedModel("test.smithy", rawModel)
      );

    this.nameResolver = getNameResolver(model, SERVICE_SHAPE_ID);

    this.underTest =
      new NativeWrapperCodegen(
        this.model,
        SERVICE_SHAPE_ID,
        ShapeId.fromParts(SERVICE_NAMESPACE, "Baz"),
        this.nameResolver
      );
  }

  @Test
  public void testGenerateValidateNativeOutput() {
    ShapeId outputShapeId = ShapeId.fromParts(
      SERVICE_NAMESPACE,
      "DoSomethingOutput"
    );
    String nativeOutputType = "Test.Foobar.DoSomethingOutput";
    final String actual =
      this.underTest.generateValidateNativeOutputMethod(
          Optional.of(outputShapeId),
          Optional.of(nativeOutputType),
          "DoSomethingWithOutput"
        )
        .toString();
    final String expected =
      NativeWrapperCodegenTestConstants.VALIDATE_NATIVE_OUTPUT.formatted(
        nativeOutputType,
        "DoSomethingWithOutput"
      );
    tokenizeAndAssertEqual(actual, expected);
  }

  @Test
  public void testGenerateOperationWrapperWithOutput() {
    String rawModel =
      """
      namespace test.foobar
      use aws.polymorph#positional
      resource Baz { operations: [DoSomethingWithOutput] }
      operation DoSomethingWithOutput { output: DoSomethingOutput }
      structure DoSomethingOutput {}
      """;
    NativeWrapperCodegen localUnderTest = setupLocalModel(rawModel);
    final String actual = localUnderTest
      .generateOperationWrapper(
        ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingWithOutput")
      )
      .toString();
    final String expected =
      NativeWrapperCodegenTestConstants.DO_OUTPUT_NOT_POSITIONAL;
    tokenizeAndAssertEqual(actual, expected);
  }

  @Test
  public void testGenerateOperationWrapperWithOutputPositional() {
    String rawModel =
      """
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
    NativeWrapperCodegen localUnderTest = setupLocalModel(rawModel);
    final String actual = localUnderTest
      .generateOperationWrapper(
        ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingWithOutput")
      )
      .toString();
    final String expected =
      NativeWrapperCodegenTestConstants.DO_OUTPUT_POSITIONAL;
    tokenizeAndAssertEqual(actual, expected);
  }

  @Test
  public void testGenerateOperationWrapperWithInput() {
    String rawModel =
      """
      namespace test.foobar
      resource Baz { operations: [DoSomethingWithInput] }
      operation DoSomethingWithInput { input: DoSomethingInput }
      structure DoSomethingInput {}
      """;
    NativeWrapperCodegen localUnderTest = setupLocalModel(rawModel);
    final String actual = localUnderTest
      .generateOperationWrapper(
        ShapeId.fromParts(SERVICE_NAMESPACE, "DoSomethingWithInput")
      )
      .toString();
    final String expected = NativeWrapperCodegenTestConstants.DO_INPUT;
    tokenizeAndAssertEqual(actual, expected);
  }

  @Test
  public void testGenerateConstructor() {
    final String className = "NativeWrapper_Baz";
    final String actual =
      this.underTest.generateConstructor(className).toString();
    final String expected = NativeWrapperCodegenTestConstants.CONSTRUCTOR;
    tokenizeAndAssertEqual(actual, expected);
  }

  @Test
  public void testGenerateClassSimple() {
    String rawModel =
      """
      namespace test.foobar
      resource Baz {}
      """;
    NativeWrapperCodegen localUnderTest = setupLocalModel(rawModel);
    final String actual = localUnderTest.generateClass().toString();
    final String expected = NativeWrapperCodegenTestConstants.SIMPLE_CLASS;
    tokenizeAndAssertEqual(actual, expected);
  }

  @Test
  public void testGenerateClassVoid() {
    String rawModel =
      """
      namespace test.foobar
      resource Baz {operations: [Do]}
      operation Do {}
      """;
    NativeWrapperCodegen localUnderTest = setupLocalModel(rawModel);
    final String actual = localUnderTest.generateClass().toString();
    final String expected = NativeWrapperCodegenTestConstants.VOID_CLASS;
    tokenizeAndAssertEqual(actual, expected);
  }

  @Test
  public void testGenerateClassComplete() {
    final String actual = this.underTest.generateClass().toString();
    final String expected = NativeWrapperCodegenTestConstants.COMPLETE_CLASS;
    tokenizeAndAssertEqual(actual, expected);
  }

  @Test
  public void testGenerate() {
    final String actual = this.underTest.generate().toString();
    final String expected = NativeWrapperCodegenTestConstants.COMPLETE;
    tokenizeAndAssertEqual(actual, expected);
  }

  NativeWrapperCodegen setupLocalModel(String rawModel) {
    Model localModel = TestModel.setupModel((builder, modelAssembler) ->
      modelAssembler.addUnparsedModel("test.smithy", rawModel)
    );
    return new NativeWrapperCodegen(
      localModel,
      SERVICE_SHAPE_ID,
      ShapeId.fromParts(SERVICE_NAMESPACE, "Baz"),
      getNameResolver(localModel, SERVICE_SHAPE_ID)
    );
  }

  @SuppressWarnings("SameParameterValue")
  protected static DotNetNameResolver getNameResolver(
    Model model,
    ShapeId shapeId
  ) {
    return new DotNetNameResolver(
      model,
      model.expectShape(shapeId, ServiceShape.class)
    );
  }
}
