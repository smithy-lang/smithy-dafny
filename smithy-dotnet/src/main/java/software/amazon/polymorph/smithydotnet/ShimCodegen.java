// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import com.google.common.annotations.VisibleForTesting;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.traits.ClientConfigTrait;
import software.amazon.polymorph.utils.Token;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.EntityShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;

import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.*;

public class ShimCodegen {
    private final Model model;
    private final ServiceShape serviceShape;
    private final DotNetNameResolver nameResolver;

    private static final String IMPL_NAME = "_impl";
    private static final String INPUT_NAME = "input";
    private static final String INTERNAL_INPUT_NAME = "internalInput";
    private static final String RESULT_NAME = "result";

    public ShimCodegen(final Model model, final ShapeId serviceShapeId) {
        this.model = model;
        this.serviceShape = model.expectShape(serviceShapeId, ServiceShape.class);
        this.nameResolver = new DotNetNameResolver(model, serviceShape);
    }

    /**
     * Returns a map of service's and all resources' shim file paths to their generated ASTs.
     */
    public Map<Path, TokenTree> generate() {
        final Map<Path, TokenTree> codeByPath = new HashMap<>();
        final TokenTree prelude = TokenTree.of(
                "using System;",
                // Conditional imports.
                // TODO: get smarter about imports. maybe just fully qualify all model-agnostic types?
                "using System.IO;",
                "using System.Collections.Generic;",
                "using Aws.Crypto;",
                // end conditional imports
                "using",
                nameResolver.namespaceForService(),
                ";"
        ).lineSeparated();

        // Service shim
        final Path serviceShimPath = Path.of(String.format("%s.cs", nameResolver.clientForService()));
        final TokenTree serviceShimCode = generateServiceShim();
        codeByPath.put(serviceShimPath, serviceShimCode.prepend(prelude));

        // Resource shims
        model.getResourceShapes()
                .stream()
                .map(ResourceShape::getId)
                .filter(resourceShapeId -> ModelUtils.isInServiceNamespace(resourceShapeId, serviceShape))
                .forEach(resourceShapeId -> {
                    final Path resourceShimPath = Path.of(
                            String.format("%s.cs", nameResolver.shimClassForResource(resourceShapeId)));
                    final TokenTree resourceShim = generateResourceShim(resourceShapeId);
                    codeByPath.put(resourceShimPath, resourceShim.prepend(prelude));
                });

        return codeByPath;
    }

    public TokenTree generateServiceShim() {
        final TokenTree header = Token.of("public static class %s".formatted(
                nameResolver.clientForService()));
        final TokenTree body = TokenTree.of(
                generateStaticImplDeclaration(),
                generateStaticOperationShims(serviceShape.getId())
        ).lineSeparated();
        return header
                .append(body.braced())
                .namespaced(Token.of(nameResolver.namespaceForService()));
    }

    public TokenTree generateStaticImplDeclaration() {
        final Optional<ShapeId> configShapeIdOptional = serviceShape.getTrait(ClientConfigTrait.class)
                .map(ClientConfigTrait::getClientConfigId);
        final TokenTree configArg = configShapeIdOptional.map(shapeId -> TokenTree.of(
                DotNetNameResolver.qualifiedTypeConverter(shapeId, TO_DAFNY),
                "(config)"
        )).orElse(TokenTree.empty());
        return Token.of("static %s %s = new %s(%s);".formatted(
                nameResolver.dafnyImplForServiceClient(),
                IMPL_NAME,
                nameResolver.dafnyImplForServiceClient(),
                configArg));
    }

    public TokenTree generateStaticOperationShims(final ShapeId entityShapeId) {
        final EntityShape entityShape = model.expectShape(entityShapeId, EntityShape.class);
        return TokenTree.of(entityShape.getAllOperations().stream().map(this::generateStaticOperationShim)).lineSeparated();
    }

    public TokenTree generateStaticOperationShim(final ShapeId operationShapeId) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);

        final String outputType = operationShape.getOutput().map(nameResolver::baseTypeForShape).orElse("void");
        final String methodName = nameResolver.methodForOperation(operationShapeId);
        final String param = operationShape.getInput()
                .map(inputShapeId -> nameResolver.baseTypeForShape(inputShapeId) + " " + INPUT_NAME)
                .orElse("");
        final TokenTree signature = Token.of("public static %s %s(%s)".formatted(outputType, methodName, param));

        final TokenTree convertInput = generateConvertInput(operationShapeId);
        final TokenTree callImpl = Token.of("%s %s = %s.%s(%s);".formatted(
                nameResolver.dafnyTypeForServiceOperationOutput(operationShape),
                RESULT_NAME,
                IMPL_NAME,
                nameResolver.methodForOperation(operationShapeId),
                operationShape.getInput().isPresent() ? INTERNAL_INPUT_NAME : ""
        ));
        final TokenTree checkAndConvertFailure = generateCheckAndConvertFailure();
        final TokenTree convertAndReturnOutput = generateConvertAndReturnOutput(operationShapeId);

        return TokenTree.of(convertInput, callImpl, checkAndConvertFailure, convertAndReturnOutput)
                .lineSeparated()
                .braced()
                .prepend(signature);
    }

    public TokenTree generateConvertInput(final ShapeId operationShapeId) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);
        return Token.of(operationShape.getInput()
                .map(inputShapeId -> "%s %s = %s(%s);".formatted(
                        nameResolver.dafnyTypeForShape(inputShapeId),
                        INTERNAL_INPUT_NAME,
                        DotNetNameResolver.qualifiedTypeConverter(inputShapeId, TO_DAFNY),
                        INPUT_NAME))
                .orElse(""));
    }

    public TokenTree generateCheckAndConvertFailure() {
        return Token.of("if (%s.is_Failure) throw %s(%s.dtor_error);"
                .formatted(
                        RESULT_NAME,
                        DotNetNameResolver.qualifiedTypeConverterForCommonError(serviceShape, FROM_DAFNY),
                        RESULT_NAME
                ));
    }

    public TokenTree generateConvertAndReturnOutput(final ShapeId operationShapeId) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);
        return Token.of(operationShape.getOutput()
                .map(outputShapeId -> "return %s(%s.dtor_value);".formatted(
                        DotNetNameResolver.qualifiedTypeConverter(outputShapeId, FROM_DAFNY),
                        RESULT_NAME))
                .orElse(""));
    }

    /**
     * Generate a shim that wraps a Dafny-compiled implementation of the given resource interface.
     *
     * TODO: generate a shim that wraps a native C# implementation (i.e. customer-implemented)
     */
    public TokenTree generateResourceShim(final ShapeId resourceShapeId) {
        final TokenTree header = Token.of("internal class %s : %s".formatted(
                nameResolver.shimClassForResource(resourceShapeId),
                nameResolver.baseClassForResource(resourceShapeId)));
        final TokenTree body = TokenTree.of(
                generateResourceImplDeclaration(resourceShapeId),
                generateResourceConstructor(resourceShapeId),
                generateOperationShims(resourceShapeId)
        ).lineSeparated();
        return header
                .append(body.braced())
                .namespaced(Token.of(nameResolver.namespaceForService()));
    }

    public TokenTree generateResourceConstructor(final ShapeId resourceShapeId) {
        return Token.of("internal %s(%s impl) { this.%s = impl; }".formatted(
                nameResolver.shimClassForResource(resourceShapeId),
                nameResolver.dafnyTypeForShape(resourceShapeId),
                IMPL_NAME));
    }

    public TokenTree generateResourceImplDeclaration(final ShapeId entityShapeId) {
        return Token.of("internal %s %s { get; }".formatted(
                nameResolver.dafnyTypeForShape(entityShapeId), IMPL_NAME));
    }

    public TokenTree generateOperationShims(final ShapeId entityShapeId) {
        final EntityShape entityShape = model.expectShape(entityShapeId, EntityShape.class);
        return TokenTree.of(entityShape.getAllOperations().stream().map(this::generateOperationShim)).lineSeparated();
    }

    public TokenTree generateOperationShim(final ShapeId operationShapeId) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);

        final String outputType = operationShape.getOutput().map(nameResolver::baseTypeForShape).orElse("void");
        final String methodName = nameResolver.abstractMethodForOperation(operationShapeId);
        final String param = operationShape.getInput()
                .map(inputShapeId -> nameResolver.baseTypeForShape(inputShapeId) + " " + INPUT_NAME)
                .orElse("");
        final TokenTree signature = Token.of("protected override %s %s(%s)".formatted(outputType, methodName, param));

        final TokenTree convertInput = generateConvertInput(operationShapeId);
        final TokenTree callImpl = Token.of("%s %s = this.%s.%s(%s);".formatted(
                nameResolver.dafnyTypeForServiceOperationOutput(operationShape),
                RESULT_NAME,
                IMPL_NAME,
                nameResolver.methodForOperation(operationShapeId),
                operationShape.getInput().isPresent() ? INTERNAL_INPUT_NAME : ""
        ));
        final TokenTree checkAndConvertFailure = generateCheckAndConvertFailure();
        final TokenTree convertAndReturnOutput = generateConvertAndReturnOutput(operationShapeId);

        return TokenTree.of(convertInput, callImpl, checkAndConvertFailure, convertAndReturnOutput)
                .lineSeparated()
                .braced()
                .prepend(signature);
    }

    @VisibleForTesting
    public Model getModel() {
        return model;
    }
}
