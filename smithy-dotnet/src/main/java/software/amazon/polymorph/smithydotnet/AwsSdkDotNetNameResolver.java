// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ListShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.TraitDefinition;
import software.amazon.smithy.utils.StringUtils;

public class AwsSdkDotNetNameResolver extends DotNetNameResolver {
    public AwsSdkDotNetNameResolver(final Model model, final ServiceShape serviceShape) {
        super(model, serviceShape);
    }

    private boolean isGeneratedInSdk(final ShapeId shapeId) {
        return ModelUtils.isInServiceNamespace(shapeId, getServiceShape());
    }

    @Override
    protected String baseTypeForString(final StringShape stringShape) {
        if (isGeneratedInSdk(stringShape.getId()) && stringShape.hasTrait(EnumTrait.class)) {
            return "%s.%s".formatted(getSdkServiceNamespace(), classForEnum(stringShape.getId()));
        }

        return super.baseTypeForString(stringShape);
    }

    @Override
    protected String baseTypeForList(final ListShape listShape) {
        final MemberShape memberShape = listShape.getMember();
        final Shape targetShape = getModel().expectShape(memberShape.getTarget());

        // The .NET AWS SDK represents a list-of-enums as a list-of-strings, even though it represents enums as the
        // corresponding enum class every where else AFAICT.
        final String memberType = targetShape.hasTrait(EnumTrait.class) ? "string" : baseTypeForMember(memberShape);

        return "System.Collections.Generic.List<%s>".formatted(memberType);
    }

    @Override
    protected String baseTypeForStructure(final StructureShape structureShape) {
        if (isGeneratedInSdk(structureShape.getId()) && !structureShape.hasTrait(TraitDefinition.class)) {
            return "%s.Model.%s".formatted(getSdkServiceNamespace(), classForStructure(structureShape.getId()));
        }

        return super.baseTypeForStructure(structureShape);
    }

    @Override
    protected String baseTypeForService(final ServiceShape serviceShape) {
        if (isGeneratedInSdk(serviceShape.getId())) {
            return "%s.IAmazon%s".formatted(getSdkServiceNamespace(), getServiceName());
        }

        return super.baseTypeForService(serviceShape);
    }

    public String implForServiceClient() {
        return "%s.Amazon%sClient".formatted(getSdkServiceNamespace(), getServiceName());
    }

    private String getServiceName() {
        return StringUtils.capitalize(getServiceShape().getId().getName());
    }

    private String getSdkServiceNamespace() {
        return "Amazon.%s".formatted(getServiceName());
    }

    public String shimClassForService() {
        return "%sShim".formatted(getServiceName());
    }

    public String baseExceptionForService() {
        return "%s.Amazon%sException".formatted(getSdkServiceNamespace(), getServiceName());
    }
}
