// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.Token;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.RequiredTrait;

import java.util.List;
import java.util.Set;

import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.FROM_DAFNY;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.TO_DAFNY;

/**
 * Generates a {@code TypeConversion} class that includes all {@link TypeConversionCodegen.TypeConverter}s needed
 * for AWS SDK-specific types.
 */
public class AwsSdkTypeConversionCodegen extends TypeConversionCodegen {
    private static final ShapeId SMITHY_STRING_SHAPE_ID = ShapeId.from("smithy.api#String");

    public AwsSdkTypeConversionCodegen(final Model model, final ShapeId serviceShapeId) {
        super(model, serviceShapeId,
                new AwsSdkDotNetNameResolver(model, model.expectShape(serviceShapeId, ServiceShape.class)));
    }

    @Override
    public Set<ShapeId> findShapeIdsToConvert() {
        final Set<ShapeId> shapeIds = super.findShapeIdsToConvert();
        shapeIds.add(SMITHY_STRING_SHAPE_ID);  // needed for converting the message of an unknown error type
        return shapeIds;
    }

    @Override
    public TypeConverter generateStructureConverter(final StructureShape structureShape) {
        if (structureShape.hasTrait(ErrorTrait.class)) {
            return generateErrorStructureConverter(structureShape);
        }

        return super.generateStructureConverter(structureShape);
    }

    @Override
    protected boolean enumListMembersAreStringsInCSharp() {
        return true;
    }

    private TypeConverter generateErrorStructureConverter(final StructureShape structureShape) {
        ModelUtils.validateErrorStructureMessageNotRequired(structureShape);
        final MemberShape messageMember = structureShape.getMember("message").orElseThrow();

        // This is also enforced by Smithy, but this serves as an extra sanity check
        final StringShape messageTarget = model.getShape(messageMember.getTarget())
                .flatMap(Shape::asStringShape)
                .orElseThrow(() -> new IllegalArgumentException("An error structure's 'message' member must be a string"));

        // Since our Dafny error traits currently require an error message, we treat empty sequences as equivalent to
        // "no message".

        final TokenTree fromDafnyBody = Token.of("""
                string message = value.message.Count == 0 ? null : %s(value.message);
                return new %s(message);
                """.formatted(
                        AwsSdkDotNetNameResolver.typeConverterForShape(messageTarget.getId(), FROM_DAFNY),
                        nameResolver.baseTypeForShape(structureShape.getId())));

        final TokenTree toDafnyBody = Token.of("""
                %s message = System.String.IsNullOrEmpty(value.Message)
                    ? Dafny.Sequence<char>.Empty
                    : %s(value.Message);
                return new %s(message);
                """.formatted(
                        nameResolver.dafnyTypeForShape(messageTarget.getId()),
                        AwsSdkDotNetNameResolver.typeConverterForShape(messageTarget.getId(), TO_DAFNY),
                        nameResolver.dafnyConcreteTypeForRegularStructure(structureShape)));

        return buildConverterFromMethodBodies(structureShape, fromDafnyBody, toDafnyBody);
    }

    TypeConverter generateAwsSdkServiceReferenceStructureConverter(final StructureShape structureShape) {
        final String sdkServiceImpl = ((AwsSdkDotNetNameResolver) nameResolver).implForServiceClient();
        final String serviceClientShim = "%s.%s".formatted(
                nameResolver.namespaceForService(),
                ((AwsSdkDotNetNameResolver) nameResolver).shimClassForService());
        final String serviceInterfaceType = nameResolver.baseTypeForShape(serviceShape.getId());

        final String throwCustomImplException =
                "throw new System.ArgumentException(\"Custom implementations of %s are not supported yet\");"
                        .formatted(serviceInterfaceType);
        final TokenTree fromDafnyBody = Token.of(
                "if (value is %s shim) { return shim._impl; }".formatted(serviceClientShim),
                throwCustomImplException);
        final TokenTree toDafnyBody = TokenTree.of(
                "if (value is %s impl) { return new %s(impl); }".formatted(sdkServiceImpl, serviceClientShim),
                throwCustomImplException);

        return buildConverterFromMethodBodies(structureShape, fromDafnyBody, toDafnyBody);
    }

    @Override
    protected String getTypeConversionNamespace() {
        return ((AwsSdkDotNetNameResolver)nameResolver).syntheticNamespaceForService();
    }
}
