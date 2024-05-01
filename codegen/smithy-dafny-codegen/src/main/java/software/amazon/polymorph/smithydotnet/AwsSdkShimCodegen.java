// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.FROM_DAFNY;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.TO_DAFNY;

import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;
import software.amazon.polymorph.utils.Token;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;

public class AwsSdkShimCodegen {

  private final Model model;
  private final ServiceShape serviceShape;
  private final AwsSdkDotNetNameResolver nameResolver;

  private static final String IMPL_NAME = "_impl";

  public AwsSdkShimCodegen(final Model model, final ServiceShape serviceShape) {
    this.model = model;
    this.serviceShape = serviceShape;
    this.nameResolver = new AwsSdkDotNetNameResolver(model, serviceShape);
  }

  public Map<Path, TokenTree> generate() {
    final Map<Path, TokenTree> codeByPath = new HashMap<>();
    final TokenTree prelude = TokenTree
      .of(
        "using System;",
        "using System.IO;",
        "using System.Collections.Generic;"
      )
      .lineSeparated();

    // Service shim
    final Path serviceShimPath = Path.of(
      String.format("%s.cs", nameResolver.shimClassForService())
    );
    final TokenTree serviceShimCode = generateServiceShim();
    codeByPath.put(serviceShimPath, serviceShimCode.prepend(prelude));

    return codeByPath;
  }

  // Why are these constructors public?
  // Because the underlying implementation is a replica
  // of the Dafny wrapper.
  // There is no _safety_ introduced here per se,
  // so making is `internal` or `private`
  // just complicates other Dafny libraries working with the wrapper.
  public TokenTree generateServiceShim() {
    final TokenTree header = Token.of(
      "public class %s : %s".formatted(
          nameResolver.shimClassForService(),
          nameResolver.dafnyTypeForShape(serviceShape.getId())
        )
    );

    final TokenTree impl = Token.of(
      "public %s %s;".formatted(nameResolver.implForServiceClient(), IMPL_NAME)
    );
    final TokenTree constructor = generateServiceShimConstructor();
    final TokenTree operationShims = TokenTree
      .of(
        serviceShape
          .getAllOperations()
          .stream()
          .map(this::generateOperationShim)
      )
      .lineSeparated();

    final TokenTree classBody = TokenTree
      .of(impl, constructor, operationShims)
      .lineSeparated();
    return header
      .append(classBody.braced())
      .namespaced(Token.of(nameResolver.syntheticNamespaceForService()));
  }

  public TokenTree generateServiceShimConstructor() {
    return Token.of(
      """
      public %s(%s impl) {
          this.%s = impl;
      }""".formatted(
          nameResolver.shimClassForService(),
          nameResolver.implForServiceClient(),
          IMPL_NAME
        )
    );
  }

  public TokenTree generateOperationShim(final ShapeId operationShapeId) {
    final OperationShape operationShape = model.expectShape(
      operationShapeId,
      OperationShape.class
    );
    final String dafnyOutputType =
      nameResolver.dafnyTypeForServiceOperationOutput(operationShape, true);
    final String implOperationName =
      nameResolver.methodForOperation(operationShapeId) + "Async";

    final TokenTree sdkRequest = Token.of(
      operationShape
        .getInput()
        .map(requestShapeId ->
          "%s sdkRequest = %s(request);".formatted(
              nameResolver.baseTypeForShape(requestShapeId),
              AwsSdkDotNetNameResolver.qualifiedTypeConverter(
                requestShapeId,
                FROM_DAFNY
              )
            )
        )
        .orElse("")
    );

    final TokenTree assignSdkResponse = Token.of(
      operationShape
        .getOutput()
        .map(responseShapeId ->
          "%s sdkResponse =".formatted(
              nameResolver.baseTypeForShape(responseShapeId)
            )
        )
        .orElse("")
    );

    final String requestArg = operationShape.getInput().isPresent()
      ? "sdkRequest"
      : "";
    final String blockOnResponse = operationShape.getOutput().isPresent()
      ? ".Result"
      : ".Wait()";
    final TokenTree callImpl = Token.of(
      "this.%s.%s(%s)%s;".formatted(
          IMPL_NAME,
          implOperationName,
          requestArg,
          blockOnResponse
        )
    );

    final TokenTree returnResponse = Token.of(
      operationShape
        .getOutput()
        .map(responseShapeId ->
          "return %s.create_Success(%s(sdkResponse));".formatted(
              dafnyOutputType,
              AwsSdkDotNetNameResolver.qualifiedTypeConverter(
                responseShapeId,
                TO_DAFNY
              )
            )
        )
        .orElse(
          "return %s.create_Success(%s);".formatted(
              dafnyOutputType,
              nameResolver.dafnyValueForUnit()
            )
        )
    );

    final TokenTree tryBody = TokenTree
      .of(assignSdkResponse, callImpl, returnResponse)
      .lineSeparated();
    final TokenTree tryBlock = Token.of("try").append(tryBody.braced());

    final String baseExceptionForService =
      nameResolver.qualifiedClassForBaseServiceException();
    final TokenTree catchBlock = Token.of(
      """
      catch (System.AggregateException aggregate) {
          return %s.create_Failure(TypeConversion.ToDafny_CommonError(aggregate.InnerException));
      } catch (System.Exception ex) {
          return %s.create_Failure(TypeConversion.ToDafny_CommonError(ex));
      }
      """.formatted(dafnyOutputType, dafnyOutputType)
    );

    final TokenTree methodSignature = generateOperationShimSignature(
      operationShape
    );
    final TokenTree methodBody = TokenTree.of(sdkRequest, tryBlock, catchBlock);
    return methodSignature.append(methodBody.braced());
  }

  private TokenTree generateOperationShimSignature(
    final OperationShape operationShape
  ) {
    final String responseType = nameResolver.dafnyTypeForServiceOperationOutput(
      operationShape
    );
    final String methodName = nameResolver.methodForOperation(
      operationShape.getId()
    );
    final String requestType = operationShape
      .getInput()
      .map(requestShapeId ->
        nameResolver.dafnyTypeForShape(requestShapeId) + " request"
      )
      .orElse("");
    return Token.of(
      "public %s %s(%s)".formatted(responseType, methodName, requestType)
    );
  }
}
