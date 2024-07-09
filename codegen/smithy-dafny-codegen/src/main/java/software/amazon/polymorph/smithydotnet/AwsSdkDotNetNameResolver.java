// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import java.util.Optional;
import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.knowledge.OperationIndex;
import software.amazon.smithy.model.shapes.ListShape;
import software.amazon.smithy.model.shapes.MapShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.TraitDefinition;
import software.amazon.smithy.utils.StringUtils;

public class AwsSdkDotNetNameResolver extends DotNetNameResolver {

  public static final String KMS_SERVICE_NAME = "KMS";
  public static final String KEY_MANAGEMENT_SERVICE_NAME =
    "KeyManagementService";
  // The following are used to resolve namespace errors when generating
  // code that uses the DynamoDBv2 service model
  public static final String DDB_NAMESPACE = "com.amazonaws.dynamodb";
  public static final String DDB_SERVICE_NAME = "DynamoDB";
  public static final String DDB_SERVICE_NAME_V2 = "DynamoDBv2";
  public static final String DDB_V2_ATTRIBUTE_VALUE =
    "Amazon.DynamoDBv2.Model.AttributeValue";
  public static final String DDB_NET_INTERFACE_NAME =
    "Amazon.DynamoDBv2.IAmazonDynamoDB";
  public static final String DDB_ATTRIBUTE_VALUE_MODEL_NAMESPACE =
    "Com.Amazonaws.Dynamodb.AttributeValue";
  public static final String REQUEST = "Request";
  public static final String RESPONSE = "Response";

  public AwsSdkDotNetNameResolver(
    final Model model,
    final ServiceShape serviceShape
  ) {
    super(model, serviceShape);
  }

  private boolean isGeneratedInSdk(final ShapeId shapeId) {
    return ModelUtils.isInServiceNamespace(shapeId, getServiceShape());
  }

  @Override
  protected String baseTypeForString(final StringShape stringShape) {
    if (
      isGeneratedInSdk(stringShape.getId()) &&
      stringShape.hasTrait(EnumTrait.class)
    ) {
      return "%s.%s".formatted(
          namespaceForService(),
          classForEnum(stringShape.getId())
        );
    }

    return super.baseTypeForString(stringShape);
  }

  @Override
  protected String baseTypeForList(final ListShape listShape) {
    final MemberShape memberShape = listShape.getMember();
    final Shape targetShape = getModel().expectShape(memberShape.getTarget());

    // The .NET AWS SDK represents a list-of-enums as a list-of-strings, even though it represents enums as the
    // corresponding enum class every where else AFAICT.
    final String memberType = targetShape.hasTrait(EnumTrait.class)
      ? "string"
      : baseTypeForMember(memberShape);

    // we need to return the name AttributeValue in the sdk not the name in the model
    if (StringUtils.equals(memberType, DDB_ATTRIBUTE_VALUE_MODEL_NAMESPACE)) {
      return "System.Collections.Generic.List<%s>".formatted(
          DDB_V2_ATTRIBUTE_VALUE
        );
    }
    return "System.Collections.Generic.List<%s>".formatted(memberType);
  }

  @Override
  protected String baseTypeForMap(MapShape mapShape) {
    final MemberShape keyShape = mapShape.getKey();
    final Shape keyTargetShape = getModel().expectShape(keyShape.getTarget());
    final MemberShape valueShape = mapShape.getValue();
    final Shape valueTargetShape = getModel()
      .expectShape(valueShape.getTarget());

    // The .NET AWS SDK represents enums as strings in map values, even though it represents enums as the
    // corresponding enum class everywhere else AFAICT.
    final String keyType = keyTargetShape.hasTrait(EnumTrait.class)
      ? "string"
      : baseTypeForMember(keyShape);
    final String valueType = valueTargetShape.hasTrait(EnumTrait.class)
      ? "string"
      : baseTypeForMember(valueShape);

    if (
      StringUtils.equals(
        valueType,
        AwsSdkDotNetNameResolver.DDB_ATTRIBUTE_VALUE_MODEL_NAMESPACE
      )
    ) {
      return "System.Collections.Generic.Dictionary<%s, %s>".formatted(
          keyType,
          AwsSdkDotNetNameResolver.DDB_V2_ATTRIBUTE_VALUE
        );
    }

    return "System.Collections.Generic.Dictionary<%s, %s>".formatted(
        keyType,
        valueType
      );
  }

  @Override
  protected String baseTypeForStructure(final StructureShape structureShape) {
    if (isGeneratedInSdk(structureShape.getId())) {
      if (structureShape.hasTrait(TraitDefinition.class)) {
        throw new IllegalArgumentException(
          "Trait definition structures have no corresponding generated type"
        );
      }
      // The NET SDK uses <operation name>Request/Response
      // rather than the structure name for operation input/output structures
      Optional<ShapeId> shapeId = Optional.of(structureShape.getId());
      Optional<OperationShape> operation = getModel()
        .getOperationShapes()
        .stream()
        .filter(o -> o.getInput().equals(shapeId))
        .findFirst();
      if (operation.isPresent()) {
        return "%s.Model.%s".formatted(
            namespaceForService(),
            operation.get().getId().getName() + REQUEST
          );
      }
      operation =
        getModel()
          .getOperationShapes()
          .stream()
          .filter(o -> o.getOutput().equals(shapeId))
          .findFirst();
      if (operation.isPresent()) {
        return "%s.Model.%s".formatted(
            namespaceForService(),
            operation.get().getId().getName() + RESPONSE
          );
      }

      // The base type of an error structure is the corresponding generated exception class
      if (structureShape.hasTrait(ErrorTrait.class)) {
        return "%s.Model.%s".formatted(
            namespaceForService(),
            classForSpecificServiceException(structureShape.getId())
          );
      }

      return "%s.Model.%s".formatted(
          namespaceForService(),
          structureShape.getId().getName()
        );
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
    // The Client Implementation MUST be DynamoDB - although the NET SDK is using DynamoDBv2
    // It does not append v2 in the client for backwards compatability purposes.
    if (StringUtils.equals(getServiceName(), DDB_SERVICE_NAME_V2)) {
      return "%s.Amazon%sClient".formatted(
          namespaceForService(),
          DDB_SERVICE_NAME
        );
    }
    return "%s.Amazon%sClient".formatted(
        namespaceForService(),
        getServiceName()
      );
  }

  public String getServiceName() {
    Optional<ServiceTrait> serviceTraitOptional = serviceShape.getTrait(
      ServiceTrait.class
    );
    if (serviceTraitOptional.isPresent()) {
      String sdkId = serviceTraitOptional.get().getSdkId();

      // Account for known legacy identifiers for a few services.
      // See the metadata at https://github.com/aws/aws-sdk-net/tree/master/generator/ServiceModels
      // for details.
      if (StringUtils.equals(sdkId, DDB_SERVICE_NAME)) {
        return StringUtils.capitalize(DDB_SERVICE_NAME_V2);
      }
      if (StringUtils.equals(sdkId, KMS_SERVICE_NAME)) {
        return KEY_MANAGEMENT_SERVICE_NAME;
      }

      return AwsSdkNameResolverHelpers.mungeSdkId(sdkId);
    } else {
      return StringUtils.capitalize(getServiceShape().getId().getName());
    }
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
    // Although using V2 of the DynamoDB Client Exceptions MUST use DynamoDB as opposed to DynamoDBv2
    return StringUtils.equals(getServiceName(), DDB_SERVICE_NAME_V2)
      ? "Amazon%sException".formatted(DDB_SERVICE_NAME)
      : "Amazon%sException".formatted(getServiceName());
  }

  public String qualifiedClassForBaseServiceException() {
    return "%s.%s".formatted(
        namespaceForService(),
        classForBaseServiceException()
      );
  }

  @Override
  public String classForSpecificServiceException(ShapeId structureShapeId) {
    String name = super.classForSpecificServiceException(structureShapeId);
    return !name.endsWith("Exception") ? "%sException".formatted(name) : name;
  }
}
