// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet.localServiceWrapper;

import software.amazon.polymorph.smithydotnet.DotNetNameResolver;
import software.amazon.polymorph.utils.DafnyNameResolverHelpers;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.Token;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;

import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;
import java.util.TreeSet;
import java.util.stream.Collectors;

import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.FROM_DAFNY;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.TO_DAFNY;

public class LocalServiceWrappedShimCodegen {
    private final Model model;
    private final ServiceShape serviceShape;
    private final LocalServiceWrappedNameResolver nameResolver;

    private static final String IMPL_NAME = "_impl";
    private static final String CONVERT_ERROR_METHOD = "ConvertError";

    public LocalServiceWrappedShimCodegen(
      final Model model,
      final ServiceShape serviceShape,
      final Path[] dependentModelPaths
    ) {
        this.model = model;
        this.serviceShape = serviceShape;
        this.nameResolver = new LocalServiceWrappedNameResolver(model, serviceShape);
    }

    public Map<Path, TokenTree> generate() {
        final Map<Path, TokenTree> codeByPath = new HashMap<>();
        final TokenTree prelude = TokenTree.of(
                "using System;",
                "using System.IO;",
                "using System.Collections.Generic;"
        ).lineSeparated();

        // Service shim
        final Path serviceShimPath = Path.of(String.format("%s.cs", nameResolver.shimClassForService()));
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
        final TokenTree header = Token.of("public class %s : %s.%s".formatted(
                nameResolver.shimClassForService(),
                DafnyNameResolverHelpers.dafnyExternNamespaceForShapeId(serviceShape.getId()),
                nameResolver.dafnyTypeForShape(serviceShape.getId())));

        final TokenTree impl = Token.of("public %s %s;".formatted(nameResolver.implForServiceClient(), IMPL_NAME));
        final TokenTree constructor = generateServiceShimConstructor();
        final TokenTree operationShims = TokenTree.of(serviceShape.getAllOperations()
                .stream()
                .map(this::generateOperationShim)).lineSeparated();
        final TokenTree errorTypeShim = generateErrorTypeShim();

        final TokenTree classBody = TokenTree.of(impl, constructor, operationShims, errorTypeShim).lineSeparated();
        return header
                .append(classBody.braced())
                .namespaced(Token.of(nameResolver.namespaceForService()));
    }

    public TokenTree generateServiceShimConstructor() {
        return Token.of("""
                public %s(%s impl) {
                    this.%s = impl;
                }""".formatted(nameResolver.shimClassForService(), nameResolver.implForServiceClient(), IMPL_NAME));
    }

    public TokenTree generateOperationShim(final ShapeId operationShapeId) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);
        final String dafnyOutputType = nameResolver.dafnyTypeForServiceOperationOutput(operationShape, true);
        final String implOperationName = nameResolver.methodForOperation(operationShapeId);

        final TokenTree unWrappedRequest = Token.of(operationShape.getInput()
                .map(requestShapeId -> "%s unWrappedRequest = %s(request);".formatted(
                        nameResolver.baseTypeForShape(requestShapeId),
                        nameResolver.qualifiedTypeConverter(requestShapeId, FROM_DAFNY)))
                .orElse(""));

        final TokenTree assignWrappedResponse = Token.of(operationShape.getOutput()
                .map(responseShapeId -> "%s wrappedResponse =".formatted(nameResolver.baseTypeForShape(responseShapeId)))
                .orElse(""));

        final String requestArg = operationShape.getInput().isPresent() ? "unWrappedRequest" : "";
        final String blockOnResponse = operationShape.getOutput().isPresent() ? ".Result" : ".Wait()";
        final TokenTree callImpl = Token.of("this.%s.%s(%s);".formatted(
                IMPL_NAME, implOperationName, requestArg));

        final TokenTree returnResponse = Token.of(operationShape.getOutput()
                .map(responseShapeId -> "return %s.create_Success(%s(wrappedResponse));".formatted(
                        dafnyOutputType,
                        nameResolver.qualifiedTypeConverter(responseShapeId, TO_DAFNY)))
                .orElse("return %s.create_Success(%s);".formatted(
                        dafnyOutputType, nameResolver.dafnyValueForUnit())));

        final TokenTree tryBody = TokenTree.of(assignWrappedResponse, callImpl, returnResponse).lineSeparated();
        final TokenTree tryBlock = Token.of("try").append(tryBody.braced());

        final String baseExceptionForService = nameResolver.qualifiedClassForBaseServiceException();
        final TokenTree catchBlock = Token.of("""
                catch (%s ex) {
                    return %s.create_Failure(this.%s(ex));
                }
                """.formatted(
                        baseExceptionForService,
                        dafnyOutputType,
                        CONVERT_ERROR_METHOD));

        final TokenTree methodSignature = generateOperationShimSignature(operationShape);
        final TokenTree methodBody = TokenTree.of(unWrappedRequest, tryBlock, catchBlock);
        return methodSignature.append(methodBody.braced());
    }

    private TokenTree generateOperationShimSignature(final OperationShape operationShape) {
        final String responseType = nameResolver.dafnyTypeForServiceOperationOutput(operationShape);
        final String methodName = nameResolver.methodForOperation(operationShape.getId());
        final String requestType = operationShape.getInput()
                .map(requestShapeId -> nameResolver.dafnyTypeForShape(requestShapeId) + " request")
                .orElse("");
        return Token.of("public %s %s(%s)".formatted(responseType, methodName, requestType));
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
        final String dafnyErrorAbstractType = DotNetNameResolver.dafnyTypeForCommonServiceError(serviceShape);
        // TODO: Add the hard coded value `Error_Opaque` DafnyNameResolver
        final String dafnyUnknownErrorType = "%s.Error_Opaque"
          .formatted(DafnyNameResolverHelpers.dafnyExternNamespaceForShapeId(serviceShape.getId()));

        // Collect into TreeSet so that we generate code in a deterministic order (lexicographic, in particular)
        final TreeSet<StructureShape> errorShapes = ModelUtils.streamServiceErrors(model, serviceShape)
                .collect(Collectors.toCollection(TreeSet::new));
        final TokenTree knownErrorCases = TokenTree.of(errorShapes.stream()
                .map(errorShape -> {
                    final ShapeId errorShapeId = errorShape.getId();
                    final String wrappedErrorType = nameResolver.baseTypeForShape(errorShapeId);
                    final String errorConverter = DotNetNameResolver.qualifiedTypeConverter(errorShapeId, TO_DAFNY);
                    return Token.of("""
                            case %s e:
                                return %s(e);
                            """.formatted(wrappedErrorType, errorConverter));
                })).lineSeparated();

        final TokenTree unknownErrorCase = Token.of("""
                default:
                    return new %s(error);
                """.formatted(dafnyUnknownErrorType));

        final TokenTree signature = Token.of("private %s %s(%s error)".formatted(
                dafnyErrorAbstractType,
                CONVERT_ERROR_METHOD,
                nameResolver.qualifiedClassForBaseServiceException()));
        final TokenTree cases = TokenTree.of(knownErrorCases, unknownErrorCase).lineSeparated();
        final TokenTree body = Token.of("switch (error)").append(cases.braced());
        return signature.append(body.braced());
    }
}
