// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet.localServiceWrapper;

import static software.amazon.polymorph.smithydotnet.TypeConversionCodegen.collectionOfErrorsToDafny;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.FROM_DAFNY;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.TO_DAFNY;

import java.nio.file.Path;
import java.util.ArrayList;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import software.amazon.polymorph.smithydafny.DafnyNameResolver;
import software.amazon.polymorph.smithydotnet.DotNetNameResolver;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.Token;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;

public class LocalServiceWrappedShimCodegen {

  private final Model model;
  private final ServiceShape serviceShape;
  private final LocalServiceWrappedNameResolver nameResolver;

  private static final String IMPL_NAME = "_impl";
  private static final String CONVERT_ERROR_METHOD = "ConvertError";

  public LocalServiceWrappedShimCodegen(
    final Model model,
    final ServiceShape serviceShape
  ) {
    this.model = model;
    this.serviceShape = serviceShape;
    this.nameResolver =
      new LocalServiceWrappedNameResolver(model, serviceShape);
  }

  public Map<Path, TokenTree> generate() {
    final Map<Path, TokenTree> codeByPath = new HashMap<>();
    final TokenTree prelude = TokenTree
      .of(
        "using System;",
        "using System.Collections.Generic;",
        "using System.IO;",
        "using System.Linq;"
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
  // of the existing Dafny LocalService.
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
    final TokenTree errorTypeShim = generateErrorTypeShim();

    final TokenTree classBody = TokenTree
      .of(impl, constructor, operationShims, errorTypeShim)
      .lineSeparated();
    return header
      .append(classBody.braced())
      .namespaced(Token.of(nameResolver.namespaceForService()));
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
    final String implOperationName = nameResolver.methodForOperation(
      operationShapeId
    );

    final TokenTree unWrappedRequest = Token.of(
      operationShape
        .getInput()
        .map(requestShapeId ->
          "%s unWrappedRequest = %s(request);".formatted(
              nameResolver.baseTypeForShape(requestShapeId),
              nameResolver.qualifiedTypeConverter(requestShapeId, FROM_DAFNY)
            )
        )
        .orElse("")
    );

    final TokenTree assignWrappedResponse = Token.of(
      operationShape
        .getOutput()
        .map(responseShapeId ->
          "%s wrappedResponse =".formatted(
              nameResolver.baseTypeForShape(responseShapeId)
            )
        )
        .orElse("")
    );

    final String requestArg = operationShape.getInput().isPresent()
      ? "unWrappedRequest"
      : "";
    final String blockOnResponse = operationShape.getOutput().isPresent()
      ? ".Result"
      : ".Wait()";
    final TokenTree callImpl = Token.of(
      "this.%s.%s(%s);".formatted(IMPL_NAME, implOperationName, requestArg)
    );

    final TokenTree returnResponse = Token.of(
      operationShape
        .getOutput()
        .map(responseShapeId ->
          "return %s.create_Success(%s(wrappedResponse));".formatted(
              dafnyOutputType,
              nameResolver.qualifiedTypeConverter(responseShapeId, TO_DAFNY)
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
      .of(unWrappedRequest, assignWrappedResponse, callImpl, returnResponse)
      .lineSeparated();
    final TokenTree tryBlock = Token.of("try").append(tryBody.braced());

    final String baseExceptionForService =
      nameResolver.qualifiedClassForBaseServiceException();
    final TokenTree catchBlock = Token.of(
      """
      catch (%s ex) {
          return %s.create_Failure(this.%s(ex));
      }
      """.formatted(
          baseExceptionForService,
          dafnyOutputType,
          CONVERT_ERROR_METHOD
        )
    );

    final TokenTree methodSignature = generateOperationShimSignature(
      operationShape
    );
    final TokenTree methodBody = TokenTree.of(tryBlock, catchBlock);
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

  /**
   * Generates a shim for converting from a "Native" LocalService-defined exception to the corresponding Dafny exception.
   * These conversions are really "through" the native runtime.
   * Since this is wrapping a LocalService,
   * probably this is Dafny types on either side.
   * <p>
   * We define this here instead of in {@link LocalServiceWrappedShimCodegen} because the base error type isn't modeled.
   */
  public TokenTree generateErrorTypeShim() {
    final String dafnyErrorAbstractType =
      DotNetNameResolver.dafnyTypeForCommonServiceError(serviceShape);
    final String dafnyUnknownErrorType =
      DotNetNameResolver.dafnyUnknownErrorTypeForServiceShape(serviceShape);

    // For errors from dependencies: pass anything from a dependency-recognized namespace into Dafny
    // This passes all unmodelled errors to the dependency type conversion
    if (
      !serviceShape.hasTrait(LocalServiceTrait.class)
    ) throw new IllegalStateException("MUST be an LocalService");
    final LocalServiceTrait localServiceTrait = serviceShape.expectTrait(
      LocalServiceTrait.class
    );

    Set<String> dependentNamespaces = ModelUtils.findAllDependentNamespaces(
      new HashSet<ShapeId>(
        Collections.singleton(localServiceTrait.getConfigId())
      ),
      model
    );

    // Dependencies may throw "unmodelled" errors that are unknown to Polymorph. Polymorph cannot write
    //   explicit code to handle these errors because it does not know about unmodelled errors.
    // This passes errors from a dependency-recognized namespace into the dependency's error handler.
    // This handles both modelled and unmodelled errors.
    TokenTree dependencyErrors = TokenTree.empty();
    if (dependentNamespaces.size() > 0) {
      List<TokenTree> casesList = new ArrayList<>();
      for (String dependentNamespace : dependentNamespaces) {
        TokenTree toAppend = TokenTree.of(
          """
          case "%1$s":
            return %2$s.Error.create_%3$s(
              %1$s.TypeConversion.ToDafny_CommonError(error)
            );""".formatted(
              DotNetNameResolver.convertToCSharpNamespaceWithSegmentMapper(
                dependentNamespace,
                DotNetNameResolver::capitalizeNamespaceSegment
              ),
              DafnyNameResolver.dafnyTypesModuleExternNamespace(
                serviceShape.getId().getNamespace()
              ),
              DafnyNameResolver.dafnyBaseModuleName(dependentNamespace)
            )
        );
        casesList.add(toAppend);
      }

      final TokenTree cases = TokenTree.of(casesList.stream()).lineSeparated();

      // This `switch` condition is based on the namespace of the exception, and not the specific exception type.
      dependencyErrors =
        Token.of("switch (error.GetType().Namespace)").append(cases.braced());
    }
    // Generate errors for local wrapped service modelled errors and unmodelled errors
    // This code generates a default unrecognized error case, which MUST be generated after all other error
    //   handlers; this includes other `switch` statements.
    // Collect into TreeSet so that we generate code in a deterministic order (lexicographic, in particular)
    final TreeSet<StructureShape> errorShapes = ModelUtils
      .streamServiceErrors(model, serviceShape)
      .collect(Collectors.toCollection(TreeSet::new));

    final TokenTree knownErrorCases = TokenTree
      .of(
        errorShapes
          .stream()
          .map(errorShape -> {
            final ShapeId errorShapeId = errorShape.getId();
            final String wrappedErrorType = nameResolver.baseTypeForShape(
              errorShapeId
            );
            final String errorConverter =
              DotNetNameResolver.qualifiedTypeConverter(errorShapeId, TO_DAFNY);
            return Token.of(
              """
              case %s e:
                  return %s(e);
              """.formatted(wrappedErrorType, errorConverter)
            );
          })
      )
      .lineSeparated();
    // CollectionOfErrors wrapper for list of exceptions
    final TokenTree collectionOfErrorsCase = collectionOfErrorsToDafny(
      serviceShape,
      nameResolver
    );

    final TokenTree unknownErrorCase = Token.of(
      """
      default:
          return new %s(error, Dafny.Sequence<char>.FromString(error.ToString()));
      """.formatted(dafnyUnknownErrorType)
    );

    final TokenTree signature = Token.of(
      "private %s %s(%s error)".formatted(
          dafnyErrorAbstractType,
          CONVERT_ERROR_METHOD,
          nameResolver.qualifiedClassForBaseServiceException()
        )
    );

    final TokenTree cases = TokenTree
      .of(knownErrorCases, collectionOfErrorsCase, unknownErrorCase)
      .lineSeparated();

    final TokenTree body = TokenTree
      .of("switch (error)")
      .append(cases.braced());
    return TokenTree
      .of(
        signature.append(
          TokenTree.of(dependencyErrors, body).lineSeparated().braced()
        )
      )
      .lineSeparated();
  }
}
