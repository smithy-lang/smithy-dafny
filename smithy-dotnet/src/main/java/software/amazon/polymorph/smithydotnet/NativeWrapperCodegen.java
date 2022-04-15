package software.amazon.polymorph.smithydotnet;

import java.util.List;
import java.util.Optional;

import software.amazon.polymorph.utils.Token;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.EntityShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;

import static software.amazon.polymorph.smithydotnet.DotNetNameResolver.classForCommonServiceException;
import static software.amazon.polymorph.smithydotnet.DotNetNameResolver.qualifiedTypeConverterForCommonError;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.*;

/**
 * NativeWrapperCodegen is called to generate a native (i.e.: in the target
 * langauge, not Dafny) Wrapper for a resource implemented in the native language.
 *
 * To be concreate, at this time, it should be called for:
 * - ClientSupplier
 * - Keyring
 * - CryptographicMaterialsManager
 *
 * Ideally, this would be done by adding a trait.
 *
 * It should generate two classes, one concreate, one abstract, in separate files:
 * - NativeWrapper_resource.cs :: concreate class
 * - NativeWrapper_resourceBase.cs :: abstract class
 *
 *
 */
public class NativeWrapperCodegen {
    public final Model model;
    public final ServiceShape serviceShape;
    public final ResourceShape resourceShape;
    public final DotNetNameResolver nameResolver;
    public final ShapeId resourceShapeId;

    protected static final String CLASS_PREFIX = "NativeWrapper_";
    protected static final String BASE_SUFFIX = "Base";
    protected static final String IMPL_NAME = "_impl";
    protected static final String NATIVE_IMPL = "nativeImpl";
    protected static final String NATIVE_INPUT = "nativeInput";
    protected static final String NATIVE_OUTPUT = "nativeOutput";
    protected static final String INPUT = "input";
    protected static final String COPYRIGHT = """
            // Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
            // SPDX-License-Identifier: Apache-2.0
            // Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
            """;
    protected static final String IGNORE_IMPORT = "// ReSharper disable thrice RedundantUsingDirective";
    protected static final String IGNORE_NAME = "// ReSharper disable once RedundantNameQualifier\n";
    protected static final List<String> UNCONDITIONAL_IMPORTS = List.of(
            "System",
            "AWS.EncryptionSDK.Core", //TODO refactor to be based on service
            "Wrappers_Compile"
    );

    public NativeWrapperCodegen(
            final Model model,
            final ShapeId serviceShapeId,
            final ShapeId resourceShapeId
    ) {
        this.model = model;
        this.serviceShape = model.expectShape(serviceShapeId, ServiceShape.class);
        this.resourceShape = model.expectShape(resourceShapeId, ResourceShape.class);
        this.nameResolver = new DotNetNameResolver(model, serviceShape);
        this.resourceShapeId = resourceShapeId;
    }

    /**
     * Returns Copyright and Import statement
     */
    public static TokenTree getPrelude() {
        final TokenTree imports = TokenTree.of(UNCONDITIONAL_IMPORTS
                .stream()
                .map("using %s;"::formatted)
                .map(Token::of)).lineSeparated();
        return TokenTree.of(COPYRIGHT)
                .append(TokenTree.of(IGNORE_IMPORT))
                .append(imports)
                .lineSeparated();
    }
}
