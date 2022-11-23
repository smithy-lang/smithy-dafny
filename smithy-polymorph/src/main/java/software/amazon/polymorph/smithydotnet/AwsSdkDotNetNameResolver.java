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
            return "%s.%s".formatted(namespaceForService(), classForEnum(stringShape.getId()));
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
        if (isGeneratedInSdk(structureShape.getId())) {
            if (structureShape.hasTrait(TraitDefinition.class)) {
                throw new IllegalArgumentException("Trait definition structures have no corresponding generated type");
            }
            if (StringUtils.equals(structureShape.getId().getNamespace(), "com.amazonaws.dynamodb") &&
                    structureShape.getId().getName().endsWith("Input")) {
                String newRequestString = structureShape.getId().getName().replace("Input", "Request");
                return "%s.Model.%s".formatted(namespaceForService(), newRequestString);
            }
            if (StringUtils.equals(structureShape.getId().getNamespace(), "com.amazonaws.dynamodb") &&
                    structureShape.getId().getName().endsWith("Output")) {
                String newResponseString = structureShape.getId().getName().replace("Output", "Response");
                return "%s.Model.%s".formatted(namespaceForService(), newResponseString);
            }
            return "%s.Model.%s".formatted(namespaceForService(), structureShape.getId().getName());
        }

        return super.baseTypeForStructure(structureShape);
    }

    @Override
    protected String baseTypeForService(final ServiceShape serviceShape) {
        if (isGeneratedInSdk(serviceShape.getId())) {
            return "%s.IAmazon%s".formatted(namespaceForService(), getServiceName());
        }

        return super.baseTypeForService(serviceShape);
    }

    public String implForServiceClient() {
        if (StringUtils.equals(getServiceName(), "DynamoDBv2")) {
            return "%s.Amazon%sClient".formatted(namespaceForService(), "DynamoDB");
        }
        return "%s.Amazon%sClient".formatted(namespaceForService(), getServiceName());
    }

    private String getServiceName() {
        if (StringUtils.equals(getServiceShape().getId().getName(), "DynamoDB_20120810")) {
            return StringUtils.capitalize("DynamoDBv2");
        }
        return StringUtils.capitalize(getServiceShape().getId().getName());
    }

    @Override
    public String namespaceForService() {
        return "Amazon.%s".formatted(getServiceName());
    }

    public String syntheticNamespaceForService() {
        return super.namespaceForService();
    }

    public String shimClassForService() {
        return "%sShim".formatted(getServiceName());
    }

    @Override
    public String classForBaseServiceException() {
        return StringUtils.equals(getServiceName(), "DynamoDBv2")
                ? "Amazon%sException".formatted("DynamoDB")
                : "Amazon%sException".formatted(getServiceName());
    }

    public String qualifiedClassForBaseServiceException() {
        return "%s.%s".formatted(namespaceForService(), classForBaseServiceException());
    }
}
