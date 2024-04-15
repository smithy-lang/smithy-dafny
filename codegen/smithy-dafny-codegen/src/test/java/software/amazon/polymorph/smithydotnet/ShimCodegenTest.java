// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import static org.junit.Assert.*;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.*;
import static software.amazon.polymorph.util.TestModel.SERVICE_NAMESPACE;
import static software.amazon.polymorph.util.TestModel.SERVICE_SHAPE_ID;

import java.util.List;
import java.util.function.BiConsumer;
import org.junit.Test;
import software.amazon.polymorph.util.TestModel;
import software.amazon.polymorph.util.Tokenizer;
import software.amazon.polymorph.util.Tokenizer.ParseToken;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;

public class ShimCodegenTest {

  // TODO: Apply ShimCodegen refactor to tests
  // https://github.com/smithy-lange/smithy-dafmy/issues/28
  private static ShimCodegen setupCodegen(
    final BiConsumer<ServiceShape.Builder, ModelAssembler> updater
  ) {
    final Model model = TestModel.setupModel(updater);
    final ServiceShape serviceShape = model.expectShape(
      SERVICE_SHAPE_ID,
      ServiceShape.class
    );
    return new ShimCodegen(model, serviceShape);
  }

  @Test
  public void testGenerateResourceShim() {
    final ShimCodegen codegen = setupCodegen((builder, modelAssembler) ->
      modelAssembler.addUnparsedModel(
        "test.smithy",
        """
        namespace %s
        resource Doer { operations: [DoIt] }
        operation DoIt {}
        """.formatted(SERVICE_NAMESPACE)
      )
    );
    final ServiceShape serviceShape = codegen
      .getModel()
      .expectShape(SERVICE_SHAPE_ID, ServiceShape.class);
    final ShapeId resourceShapeId = ShapeId.fromParts(
      SERVICE_NAMESPACE,
      "Doer"
    );

    final String commonErrorTypeConverter = codegen
      .getNameResolver()
      .qualifiedTypeConverterForCommonError(serviceShape, FROM_DAFNY);
    final List<ParseToken> expectedTokens = Tokenizer.tokenize(
      """
      namespace Test.Foobar {
          internal class Doer : DoerBase {
              internal readonly test.foobar.internaldafny.types.IDoer _impl;
              internal Doer(test.foobar.internaldafny.types.IDoer impl) { this._impl = impl; }
              protected override void _DoIt() {
                  Wrappers_Compile._IResult<_System._ITuple0, test.foobar.internaldafny.types._IError> result =
                          this._impl.DoIt();
                  if (result.is_Failure) throw %s(result.dtor_error);
              }
          }
      }
      """.formatted(commonErrorTypeConverter)
    );

    final String actualCode = codegen
      .generateResourceShim(resourceShapeId)
      .toString();
    final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

    assertEquals(expectedTokens, actualTokens);
  }

  @Test
  public void testGenerateResourceConstructor() {
    final ShimCodegen codegen = setupCodegen((builder, modelAssembler) ->
      modelAssembler.addUnparsedModel(
        "test.smithy",
        """
        namespace %s
        resource Thing {}
        """.formatted(SERVICE_NAMESPACE)
      )
    );
    final ShapeId resourceShapeId = ShapeId.fromParts(
      SERVICE_NAMESPACE,
      "Thing"
    );

    final List<ParseToken> expectedTokens = Tokenizer.tokenize(
      "internal Thing(test.foobar.internaldafny.types.IThing impl) { this._impl = impl; }"
    );

    final String actualCode = codegen
      .generateResourceConstructor(resourceShapeId)
      .toString();
    final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

    assertEquals(expectedTokens, actualTokens);
  }

  @Test
  public void testGenerateOperationShims() {
    final ShimCodegen codegen = setupCodegen((builder, modelAssembler) ->
      modelAssembler.addUnparsedModel(
        "test.smithy",
        """
        namespace %s
        resource Doer { operations: [DoThis, DoThat] }
        operation DoThis {}
        operation DoThat {}
        """.formatted(SERVICE_NAMESPACE)
      )
    );
    final ServiceShape serviceShape = codegen
      .getModel()
      .expectShape(SERVICE_SHAPE_ID, ServiceShape.class);
    final ShapeId resourceShapeId = ShapeId.fromParts(
      SERVICE_NAMESPACE,
      "Doer"
    );

    final String commonErrorTypeConverter = codegen
      .getNameResolver()
      .qualifiedTypeConverterForCommonError(serviceShape, FROM_DAFNY);
    final List<ParseToken> expectedTokens = Tokenizer.tokenize(
      """
      protected override void _DoThis() {
          Wrappers_Compile._IResult<_System._ITuple0, test.foobar.internaldafny.types._IError> result =
                  this._impl.DoThis();
          if (result.is_Failure) throw %1$s(result.dtor_error);
      }
      protected override void _DoThat() {
          Wrappers_Compile._IResult<_System._ITuple0, test.foobar.internaldafny.types._IError> result =
                  this._impl.DoThat();
          if (result.is_Failure) throw %1$s(result.dtor_error);
      }
      """.formatted(commonErrorTypeConverter)
    );

    final String actualCode = codegen
      .generateOperationShims(resourceShapeId)
      .toString();
    final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

    assertEquals(expectedTokens, actualTokens);
  }

  @Test
  public void testGenerateOperationShimInputOnly() {
    final ShimCodegen codegen = setupCodegen((builder, modelAssembler) ->
      modelAssembler.addUnparsedModel(
        "test.smithy",
        """
        namespace %s
        operation DoIt { input: Input }
        structure Input {}
        """.formatted(SERVICE_NAMESPACE)
      )
    );
    final ServiceShape serviceShape = codegen
      .getModel()
      .expectShape(SERVICE_SHAPE_ID, ServiceShape.class);
    final ShapeId operationShapeId = ShapeId.fromParts(
      SERVICE_NAMESPACE,
      "DoIt"
    );
    final ShapeId inputShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Input");

    final String commonErrorTypeConverter = codegen
      .getNameResolver()
      .qualifiedTypeConverterForCommonError(serviceShape, FROM_DAFNY);
    final List<ParseToken> expectedTokens = Tokenizer.tokenize(
      """
      protected override void _DoIt(Test.Foobar.Input input) {
          test.foobar.internaldafny.types._IInput internalInput = %s(input);
          Wrappers_Compile._IResult<_System._ITuple0, test.foobar.internaldafny.types._IError>
                  result = this._impl.DoIt(internalInput);
          if (result.is_Failure) throw %s(result.dtor_error);
      }
      """.formatted(
          DotNetNameResolver.qualifiedTypeConverter(inputShapeId, TO_DAFNY),
          commonErrorTypeConverter
        )
    );

    final String actualCode = codegen
      .generateOperationShim(operationShapeId)
      .toString();
    final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

    assertEquals(expectedTokens, actualTokens);
  }

  @Test
  public void testGenerateOperationShimOutputOnly() {
    final ShimCodegen codegen = setupCodegen((builder, modelAssembler) ->
      modelAssembler.addUnparsedModel(
        "test.smithy",
        """
        namespace %s
        operation DoIt { output: Output }
        structure Output {}
        """.formatted(SERVICE_NAMESPACE)
      )
    );
    final ServiceShape serviceShape = codegen
      .getModel()
      .expectShape(SERVICE_SHAPE_ID, ServiceShape.class);
    final ShapeId operationShapeId = ShapeId.fromParts(
      SERVICE_NAMESPACE,
      "DoIt"
    );
    final ShapeId outputShapeId = ShapeId.fromParts(
      SERVICE_NAMESPACE,
      "Output"
    );

    final String commonErrorTypeConverter = codegen
      .getNameResolver()
      .qualifiedTypeConverterForCommonError(serviceShape, FROM_DAFNY);
    final List<ParseToken> expectedTokens = Tokenizer.tokenize(
      """
      protected override Test.Foobar.Output _DoIt() {
          Wrappers_Compile._IResult<test.foobar.internaldafny.types._IOutput, test.foobar.internaldafny.types._IError>
                  result = this._impl.DoIt();
          if (result.is_Failure) throw %s(result.dtor_error);
          return %s(result.dtor_value);
      }
      """.formatted(
          commonErrorTypeConverter,
          DotNetNameResolver.qualifiedTypeConverter(outputShapeId, FROM_DAFNY)
        )
    );

    final String actualCode = codegen
      .generateOperationShim(operationShapeId)
      .toString();
    final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

    assertEquals(expectedTokens, actualTokens);
  }

  @Test
  public void testGenerateOperationShimInputAndOutput() {
    final ShimCodegen codegen = setupCodegen((builder, modelAssembler) -> {
      modelAssembler.addUnparsedModel(
        "test.smithy",
        """
        namespace %s
        operation DoIt { input: Input, output: Output }
        structure Input {}
        structure Output {}
        """.formatted(SERVICE_NAMESPACE)
      );
    });
    final ServiceShape serviceShape = codegen
      .getModel()
      .expectShape(SERVICE_SHAPE_ID, ServiceShape.class);
    final ShapeId operationShapeId = ShapeId.fromParts(
      SERVICE_NAMESPACE,
      "DoIt"
    );
    final ShapeId inputShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Input");
    final ShapeId outputShapeId = ShapeId.fromParts(
      SERVICE_NAMESPACE,
      "Output"
    );

    final String commonErrorTypeConverter = codegen
      .getNameResolver()
      .qualifiedTypeConverterForCommonError(serviceShape, FROM_DAFNY);
    final List<ParseToken> expectedTokens = Tokenizer.tokenize(
      """
      protected override Test.Foobar.Output _DoIt(Test.Foobar.Input input) {
          test.foobar.internaldafny.types._IInput internalInput = %s(input);
          Wrappers_Compile._IResult<test.foobar.internaldafny.types._IOutput, test.foobar.internaldafny.types._IError>
                  result = this._impl.DoIt(internalInput);
          if (result.is_Failure) throw %s(result.dtor_error);
          return %s(result.dtor_value);
      }
      """.formatted(
          DotNetNameResolver.qualifiedTypeConverter(inputShapeId, TO_DAFNY),
          commonErrorTypeConverter,
          DotNetNameResolver.qualifiedTypeConverter(outputShapeId, FROM_DAFNY)
        )
    );

    final String actualCode = codegen
      .generateOperationShim(operationShapeId)
      .toString();
    final List<ParseToken> actualTokens = Tokenizer.tokenize(actualCode);

    assertEquals(expectedTokens, actualTokens);
  }
}
