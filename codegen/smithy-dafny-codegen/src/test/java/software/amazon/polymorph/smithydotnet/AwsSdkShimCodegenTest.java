// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import static org.junit.Assert.assertEquals;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.FROM_DAFNY;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.TO_DAFNY;
import static software.amazon.polymorph.util.Tokenizer.tokenizeAndAssertEqual;

import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiConsumer;
import org.junit.Test;
import software.amazon.polymorph.util.TestModel;
import software.amazon.polymorph.util.Tokenizer;
import software.amazon.polymorph.util.Tokenizer.ParseToken;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;

public class AwsSdkShimCodegenTest {

  private static final String SERVICE_NAMESPACE = "com.amazonaws.foobar";
  private static final String SERVICE_NAME = "FoobarService";
  private static final ShapeId SERVICE_SHAPE_ID = ShapeId.fromParts(
    SERVICE_NAMESPACE,
    SERVICE_NAME
  );

  private static AwsSdkShimCodegen setupCodegen(
    final BiConsumer<ServiceShape.Builder, ModelAssembler> updater
  ) {
    final Model model = TestModel.setupModel((builder, assembler) -> {
      builder.id(SERVICE_SHAPE_ID);
      updater.accept(builder, assembler);
    });
    final ServiceShape serviceShape = model.expectShape(
      SERVICE_SHAPE_ID,
      ServiceShape.class
    );
    return new AwsSdkShimCodegen(model, serviceShape);
  }

  //TODO: apply AwsSdkShimCodegen refactor to tests
  @Test
  public void testGenerateEmptyService() {
    final AwsSdkShimCodegen codegen = setupCodegen(
      (_builder, _modelAssembler) -> {}
    );
    final Map<Path, TokenTree> codeByPath = codegen.generate();
    final Path shimPath = Path.of("FoobarServiceShim.cs");
    assert codeByPath.keySet().equals(Set.of(shimPath));

    final String actual = codeByPath.get(shimPath).toString();

    final String expected =
      """
      using System;
      using System.IO;
      using System.Collections.Generic;

      namespace Com.Amazonaws.Foobar {
          public class FoobarServiceShim : software.amazon.cryptography.services.foobar.internaldafny.types.IFoobarServiceClient {
              public Amazon.FoobarService.AmazonFoobarServiceClient _impl;

              public FoobarServiceShim(Amazon.FoobarService.AmazonFoobarServiceClient impl) {
                  this._impl = impl;
              }
          }
      }
      """;

    tokenizeAndAssertEqual(actual, expected);
  }

  @Test
  public void testGenerateServiceShim() {
    final ShapeId inputOperation = ShapeId.fromParts(
      SERVICE_NAMESPACE,
      "DoInput"
    );
    final ShapeId outputOperation = ShapeId.fromParts(
      SERVICE_NAMESPACE,
      "DoOutput"
    );
    final AwsSdkShimCodegen codegen = setupCodegen(
      (builder, modelAssembler) -> {
        builder.addOperation(inputOperation);
        builder.addOperation(outputOperation);
        modelAssembler.addUnparsedModel(
          "test.smithy",
          """
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
          """
        );
      }
    );
    final List<ParseToken> actualTokens = Tokenizer.tokenize(
      codegen.generateServiceShim().toString()
    );

    final String expectedShimConstructor = codegen
      .generateServiceShimConstructor()
      .toString();
    final String expectedInputOperationShim = codegen
      .generateOperationShim(inputOperation)
      .toString();
    final String expectedOutputOperationShim = codegen
      .generateOperationShim(outputOperation)
      .toString();
    final List<ParseToken> expectedTokens = Tokenizer.tokenize(
      """
      namespace Com.Amazonaws.Foobar {
          public class FoobarServiceShim : software.amazon.cryptography.services.foobar.internaldafny.types.IFoobarServiceClient {
              public Amazon.FoobarService.AmazonFoobarServiceClient _impl;
              %s
              %s
              %s
          }
      }
      """.formatted(
          expectedShimConstructor,
          expectedInputOperationShim,
          expectedOutputOperationShim
        )
    );

    assertEquals(expectedTokens, actualTokens);
  }

  @Test
  public void testGenerateOperationShim() {
    final ShapeId operationShapeId = ShapeId.fromParts(SERVICE_NAMESPACE, "Go");
    final ShapeId requestShapeId = ShapeId.fromParts(
      SERVICE_NAMESPACE,
      "GoRequest"
    );
    final ShapeId responseShapeId = ShapeId.fromParts(
      SERVICE_NAMESPACE,
      "GoResponse"
    );
    final AwsSdkShimCodegen codegen = setupCodegen(
      (builder, modelAssembler) -> {
        builder.addOperation(operationShapeId);
        modelAssembler.addUnparsedModel(
          "test.smithy",
          """
          namespace com.amazonaws.foobar
          operation Go {
              input: GoRequest,
              output: GoResponse,
              errors: [Crash],
          }
          structure GoRequest {}
          structure GoResponse {}
          @error("client") structure Crash { message: String }
          """
        );
      }
    );

    final List<ParseToken> actualTokens = Tokenizer.tokenize(
      codegen.generateOperationShim(operationShapeId).toString()
    );

    final String resultTypeParams =
      "%s, %s".formatted(
          "software.amazon.cryptography.services.foobar.internaldafny.types._IGoResponse",
          "software.amazon.cryptography.services.foobar.internaldafny.types._IError"
        );
    final String requestFromDafnyConverter =
      AwsSdkDotNetNameResolver.qualifiedTypeConverter(
        requestShapeId,
        FROM_DAFNY
      );
    final String responseToDafnyConverter =
      AwsSdkDotNetNameResolver.qualifiedTypeConverter(
        responseShapeId,
        TO_DAFNY
      );
    final List<ParseToken> expectedTokens = Tokenizer.tokenize(
      """
      public Wrappers_Compile._IResult<%1$s> Go(software.amazon.cryptography.services.foobar.internaldafny.types._IGoRequest request) {
          Amazon.FoobarService.Model.GoRequest sdkRequest = %2$s(request);
          try {
              Amazon.FoobarService.Model.GoResponse sdkResponse =
                  this._impl.GoAsync(sdkRequest).Result;
              return Wrappers_Compile.Result<%1$s>.create_Success(%3$s(sdkResponse));
          }
          catch (System.AggregateException aggregate) {
              return Wrappers_Compile.Result<%1$s>.create_Failure(TypeConversion.ToDafny_CommonError(aggregate.InnerException));
          }
          catch (System.Exception ex) {
              return Wrappers_Compile.Result<%1$s>.create_Failure(TypeConversion.ToDafny_CommonError(ex));
          }
      }
      """.formatted(
          resultTypeParams,
          requestFromDafnyConverter,
          responseToDafnyConverter
        )
    );

    assertEquals(expectedTokens, actualTokens);
  }
}
