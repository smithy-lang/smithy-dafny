// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import java.util.List;

import software.amazon.polymorph.utils.Token;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;

/**
 * NativeWrapperCodegen is called to generate a Native (i.e.: in the target
 * langauge, not Dafny) Wrapper for a resource implemented in the native language.
 *
 * To be concreate, at this time, it should be called for:
 * - ClientSupplier
 * - Keyring
 * - CryptographicMaterialsManager
 */
public abstract class NativeWrapperCodegen {
    public final Model model;
    public final ServiceShape serviceShape;
    public final ResourceShape resourceShape;
    public final DotNetNameResolver nameResolver;
    public final ShapeId resourceShapeId;

    protected static final String CLASS_PREFIX = "NativeWrapper";
    protected static final String NATIVE_BASE_PROPERTY = "_impl";
    protected static final String NATIVE_IMPL_INPUT = "nativeImpl";
    protected static final String NATIVE_INPUT = "nativeInput";
    protected static final String NATIVE_OUTPUT = "nativeOutput";
    protected static final String INPUT = "input";
    protected static final String IGNORE_IMPORT =
            """
            // ReSharper disable RedundantUsingDirective
            // ReSharper disable RedundantNameQualifier
            // ReSharper disable SuggestVarOrType_SimpleTypes
            """;
    protected static final List<String> UNCONDITIONAL_IMPORTS = List.of(
            "System",
            "AWS.EncryptionSDK.Core", //TODO refactor to be based on service
            "Wrappers_Compile"
    );

    public NativeWrapperCodegen(
            final Model model,
            final ShapeId serviceShapeId,
            final ShapeId resourceShapeId,
            final DotNetNameResolver nameResolver
    ) {
        this.model = model;
        this.serviceShape = model.expectShape(serviceShapeId, ServiceShape.class);
        this.resourceShape = model.expectShape(resourceShapeId, ResourceShape.class);
        this.nameResolver = nameResolver;
        this.resourceShapeId = resourceShapeId;
    }

    /**
     * Returns Import statement
     */
    public static TokenTree getPrelude() {
        final TokenTree imports = TokenTree.of(UNCONDITIONAL_IMPORTS
                .stream()
                .map("using %s;"::formatted)
                .map(Token::of)).lineSeparated();
        return TokenTree.of(IGNORE_IMPORT)
                .append(imports);
    }

    public TokenTree generate() {
        throw new UnsupportedOperationException("Not supported by abstract");
    }
}
