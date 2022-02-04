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
        final TokenTree header = Token.of("public class %s : %s".formatted(
                nameResolver.clientForService(),
                nameResolver.baseClientForService()));
        final TokenTree body = TokenTree.of(
                generateServiceImplDeclaration(),
                generateServiceConstructor(),
                generateOperationShims(serviceShape.getId())
        ).lineSeparated();
        return header
                .append(body.braced())
                .namespaced(Token.of(nameResolver.namespaceForService()));
    }

    public TokenTree generateServiceConstructor() {
        final Optional<ShapeId> configShapeIdOptional = serviceShape.getTrait(ClientConfigTrait.class)
                .map(ClientConfigTrait::getClientConfigId);

        final TokenTree configParam = configShapeIdOptional.map(shapeId -> TokenTree.of(
                nameResolver.baseTypeForShape(shapeId),
                "config"
        )).orElse(TokenTree.empty());
        final TokenTree baseCtorCall = configShapeIdOptional.isPresent()
                ? Token.of(": base(config)") : TokenTree.empty();
        final TokenTree configArg = configShapeIdOptional.map(shapeId -> TokenTree.of(
                DotNetNameResolver.qualifiedTypeConverter(shapeId, TO_DAFNY),
                "(config)"
        )).orElse(TokenTree.empty());
        return Token.of("public %s(%s) %s { this.%s = new %s(%s); }".formatted(
                nameResolver.clientForService(),
                configParam,
                baseCtorCall,
                IMPL_NAME,
                nameResolver.dafnyImplForServiceClient(),
                configArg));
    }

    public TokenTree generateServiceImplDeclaration() {
        return Token.of("private %s %s;".formatted(nameResolver.dafnyImplForServiceClient(), IMPL_NAME));
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
                .map(inputShapeId -> nameResolver.baseTypeForShape(inputShapeId) + " input")
                .orElse("");
        final TokenTree signature = Token.of("protected override %s %s(%s)".formatted(outputType, methodName, param));

        final TokenTree convertInput = Token.of(operationShape.getInput()
                .map(inputShapeId -> "%s internalInput = %s(input);".formatted(
                        nameResolver.dafnyTypeForShape(inputShapeId),
                        DotNetNameResolver.qualifiedTypeConverter(inputShapeId, TO_DAFNY)))
                .orElse(""));
        final TokenTree callImpl = Token.of("%s result = this.%s.%s(%s);".formatted(
                nameResolver.dafnyTypeForServiceOperationOutput(operationShape),
                IMPL_NAME,
                nameResolver.methodForOperation(operationShapeId),
                operationShape.getInput().isPresent() ? "internalInput" : ""
        ));
        final TokenTree checkAndConvertFailure = Token.of("if (result.is_Failure) throw %s(result.dtor_error);"
                .formatted(DotNetNameResolver.qualifiedTypeConverterForCommonError(serviceShape, FROM_DAFNY)));
        final TokenTree convertAndReturnOutput = Token.of(operationShape.getOutput()
                .map(outputShapeId -> "return %s(result.dtor_value);".formatted(
                        DotNetNameResolver.qualifiedTypeConverter(outputShapeId, FROM_DAFNY)))
                .orElse(""));

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
