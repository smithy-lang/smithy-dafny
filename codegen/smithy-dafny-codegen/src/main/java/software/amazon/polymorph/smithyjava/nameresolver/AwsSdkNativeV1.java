// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.nameresolver;

import static software.amazon.polymorph.smithyjava.nameresolver.Constants.SHAPE_TYPES_LIST_SET;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.ParameterizedTypeName;
import com.squareup.javapoet.TypeName;
import java.util.List;
import java.util.Map;
import java.util.Set;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.TraitDefinition;
import software.amazon.smithy.utils.StringUtils;

/**
 * There are certain assumptions we can/have to make about
 * Types from the AWS SDK for Java V1 libraries.
 */
public class AwsSdkNativeV1 extends Native {

  public AwsSdkNativeV1(final ServiceShape serviceShape, final Model model) {
    super(
      packageNameForAwsSdkV1Shape(serviceShape),
      serviceShape,
      model,
      defaultModelPackageName(packageNameForAwsSdkV1Shape(serviceShape)),
      CodegenSubject.AwsSdkVersion.V1
    );
    checkForAwsServiceConstants();
  }

  // The values of these maps are NOT in smithy models and thus must be hard-coded
  public static final Map<
    String,
    String
  > AWS_SERVICE_NAMESPACE_TO_CLIENT_INTERFACE;
  public static final Map<
    String,
    String
  > AWS_SERVICE_NAMESPACE_TO_BASE_EXCEPTION;

  static {
    // These are NOT in the service's model package
    // i.e: kms : com.amazonaws.kms.AWSKMS
    AWS_SERVICE_NAMESPACE_TO_CLIENT_INTERFACE =
      Map.ofEntries(
        Map.entry("com.amazonaws.kms", "AWSKMS"),
        Map.entry("com.amazonaws.dynamodb", "AmazonDynamoDB"),
        Map.entry("com.amazonaws.s3", "AmazonS3")
      );
    // These are in the service's model package
    // i.e.: kms : com.amazonaws.kms.model.AWSKMSException
    AWS_SERVICE_NAMESPACE_TO_BASE_EXCEPTION =
      Map.ofEntries(
        Map.entry("com.amazonaws.kms", "AWSKMSException"),
        Map.entry("com.amazonaws.dynamodb", "AmazonDynamoDBException"),
        Map.entry("com.amazonaws.s3", "AmazonS3Exception")
      );
  }

  /** Validates that Polymorph knows non-smithy modeled constants for an AWS Service */
  private void checkForAwsServiceConstants() {
    String namespace = serviceShape.getId().getNamespace();
    checkForAwsServiceConstants(namespace);
  }

  public static void checkForAwsServiceConstants(String namespace) {
    boolean knowBaseException =
      AWS_SERVICE_NAMESPACE_TO_BASE_EXCEPTION.containsKey(namespace);
    if (!knowBaseException) {
      throw new IllegalArgumentException(
        "Polymorph does not know this service's Base Exception: %s".formatted(
            namespace
          )
      );
    }
    boolean knowClientInterface =
      AWS_SERVICE_NAMESPACE_TO_CLIENT_INTERFACE.containsKey(namespace);
    if (!knowClientInterface) {
      throw new IllegalArgumentException(
        "Polymorph does not know this service's Client Interface: %s".formatted(
            namespace
          )
      );
    }
  }

  /**
   * Throws IllegalArgumentException if shapeId is not in namespace
   */
  private void checkInServiceNamespace(final ShapeId shapeId) {
    if (!isInServiceNameSpace(shapeId)) {
      throw new IllegalArgumentException(
        "ShapeId %s is not in this namespace %s".formatted(
            shapeId,
            serviceShape.getId().getNamespace()
          )
      );
    }
  }

  /**
   * <p>In the AWS SDK Java V1,
   * structures never return Enums, only their string representation.
   * Thus, any methods that handle the result of a get Enum value
   * must handle String, not the Enum reference.</p>
   *
   * <p>At this time, we believe that is only needs to be called
   * for aggregates other than structure or union,
   * as only Aggregate converters will indirectly deal with enums.</p>
   *
   * <p>Any direct involvement with Enums are safe,
   * since we overload the enum converter methods.</p>
   **/
  private TypeName typeForShapeNoEnum(ShapeId shapeId) {
    final Shape shape = model.expectShape(shapeId);
    if (shape.hasTrait(EnumTrait.class)) {
      return classForString();
    }
    if (SHAPE_TYPES_LIST_SET.contains(shape.getType())) {
      return typeForListSetOrMapNoEnum(shapeId);
    }
    return typeForShape(shapeId);
  }

  @SuppressWarnings("OptionalGetWithoutIsPresent")
  public ParameterizedTypeName typeForListSetOrMapNoEnum(
    final ShapeId shapeId
  ) {
    final Shape shape = model
      .getShape(shapeId)
      .orElseThrow(() ->
        new IllegalStateException("Cannot find shape " + shapeId)
      );
    return switch (shape.getType()) {
      case LIST -> ParameterizedTypeName.get(
        ClassName.get(List.class),
        typeForShapeNoEnum(shape.asListShape().get().getMember().getTarget())
      );
      case SET -> ParameterizedTypeName.get(
        ClassName.get(Set.class),
        typeForShapeNoEnum(shape.asSetShape().get().getMember().getTarget())
      );
      case MAP -> ParameterizedTypeName.get(
        ClassName.get(Map.class),
        typeForShapeNoEnum(shape.asMapShape().get().getKey().getTarget()),
        typeForShapeNoEnum(shape.asMapShape().get().getValue().getTarget())
      );
      default -> throw new IllegalStateException(
        "typeForListOrSetNoEnum only accepts LIST or SET. Got: " +
        shape.getType() +
        " for ShapeId: " +
        shapeId
      );
    };
  }

  public ClassName classNameForAwsSdkShape(final Shape shape) {
    return ClassName.get(
      defaultModelPackageName(packageNameForAwsSdkV1Shape(shape)),
      StringUtils.capitalize(shape.getId().getName())
    );
  }

  @Override
  public ClassName classNameForStructure(final Shape shape) {
    if (!(shape.isUnionShape() || shape.isStructureShape())) {
      throw new IllegalArgumentException(
        "typeForStructure should only be called for Structures or Unions. ShapeId: %s".formatted(
            shape.getId()
          )
      );
    }
    if (shape.hasTrait(TraitDefinition.class)) {
      throw new IllegalArgumentException(
        "Trait definition structures have no corresponding generated type"
      );
    }
    // check if this Shape is in AWS SDK for Java V1 package
    if (AwsSdkNameResolverHelpers.isInAwsSdkNamespace(shape.getId())) {
      return classNameForAwsSdkShape(shape);
    }
    return super.classNameForStructure(shape);
  }

  /** The AWS SDK for Java V1 replaces
   *  the last 'Response' with 'Result'
   *  in operation outputs.
   */
  public TypeName typeForOperationOutput(final ShapeId shapeId) {
    StructureShape shape = model.expectShape(shapeId, StructureShape.class);
    ClassName smithyName = classNameForStructure(shape);
    if (smithyName.simpleName().endsWith("Response")) {
      return ClassName.get(
        smithyName.packageName(),
        smithyName
          .simpleName()
          .substring(0, smithyName.simpleName().lastIndexOf("Response")) +
        "Result"
      );
    }
    return smithyName;
  }

  public static ClassName classNameForServiceClient(ServiceShape shape) {
    String awsServiceSmithyNamespace = shape.toShapeId().getNamespace();
    checkForAwsServiceConstants(awsServiceSmithyNamespace);
    return ClassName.get(
      packageNameForAwsSdkV1Shape(shape),
      AWS_SERVICE_NAMESPACE_TO_CLIENT_INTERFACE.get(awsServiceSmithyNamespace)
    );
  }

  /**
   * Returns the ClassName for an AWS Service's Base Exception.
   * <p>
   * To be clear, a Base Exception is concrete.
   * But all of a service's other exceptions extend it.
   */
  public ClassName baseErrorForService() {
    return ClassName.get(
      modelPackage,
      AWS_SERVICE_NAMESPACE_TO_BASE_EXCEPTION.get(
        serviceShape.getId().getNamespace()
      )
    );
  }

  public static String packageNameForService(final String awsServiceName) {
    String rtn = awsServiceName;
    if (awsServiceName.equals("dynamodb")) {
      rtn = "dynamodbv2";
    }
    return "com.amazonaws.services.%s".formatted(rtn);
  }

  static String packageNameForAwsSdkV1Shape(final Shape shape) {
    String awsServiceName = AwsSdkNameResolverHelpers.awsServiceNameFromShape(
      shape
    );
    return packageNameForService(awsServiceName);
  }

  public static String defaultModelPackageName(final String packageName) {
    return "%s.model".formatted(packageName);
  }
}
