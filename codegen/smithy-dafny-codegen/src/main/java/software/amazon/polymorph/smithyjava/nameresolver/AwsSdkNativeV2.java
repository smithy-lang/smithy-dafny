// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.nameresolver;

import static software.amazon.polymorph.smithyjava.nameresolver.AwsSdkV2NameResolverUtils.isAttributeValueType;
import static software.amazon.polymorph.smithyjava.nameresolver.AwsSdkV2NameResolverUtils.tokenToUncapitalizeInShape;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.SHAPE_TYPES_LIST_SET_MAP;
import static software.amazon.smithy.utils.StringUtils.uncapitalize;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.ParameterizedTypeName;
import com.squareup.javapoet.TypeName;
import java.util.List;
import java.util.Map;
import java.util.Set;
import software.amazon.awssdk.codegen.model.service.ServiceModel;
import software.amazon.awssdk.codegen.naming.DefaultNamingStrategy;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.polymorph.smithyjava.generator.awssdk.v2.JavaAwsSdkV2;
import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ShapeType;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.TraitDefinition;
import software.amazon.smithy.utils.StringUtils;

/**
 * There are certain assumptions we can/have to make about
 * Types from the AWS SDK for Java V2 libraries.
 */
public class AwsSdkNativeV2 extends Native {

  private final DefaultNamingStrategy awsSDKNaming;

  public AwsSdkNativeV2(final ServiceShape serviceShape, final Model model) {
    super(
      packageNameForAwsSdkV2Shape(serviceShape),
      serviceShape,
      model,
      defaultModelPackageName(packageNameForAwsSdkV2Shape(serviceShape)),
      CodegenSubject.AwsSdkVersion.V2
    );
    checkForAwsServiceConstants();
    awsSDKNaming = new DefaultNamingStrategy(new ServiceModel(), null);
  }

  // The values of these maps are NOT in smithy models and thus must be hard-coded
  private static final Map<
    String,
    String
  > AWS_SERVICE_NAMESPACE_TO_CLIENT_INTERFACE;
  private static final Map<
    String,
    String
  > AWS_SERVICE_NAMESPACE_TO_BASE_EXCEPTION;
  private static final Map<String, String> AWS_SERVICE_NAMESPACE_TO_SHORT_NAME;

  static {
    // The namespaces used as keys in these maps correspond to the Smithy namespace,
    // NOT the SDK V2 namespace.
    // Smithy namespace: com.amazonaws.X
    // AWSSDK V2 namespace: software.amazon.awssdk.X

    // These clients are NOT located in the services' model package;
    // they are located in its parent namespace.
    // i.e: kms : software.amazon.awssdk.kms.KmsClient
    AWS_SERVICE_NAMESPACE_TO_CLIENT_INTERFACE =
      Map.ofEntries(
        Map.entry("com.amazonaws.kms", "KmsClient"),
        Map.entry("com.amazonaws.dynamodb", "DynamoDbClient"),
        Map.entry("com.amazonaws.s3", "S3Client")
      );
    // These exception are located in the services' model package.
    // i.e.: kms : software.amazon.awssdk.kms.model.KmsException
    AWS_SERVICE_NAMESPACE_TO_BASE_EXCEPTION =
      Map.ofEntries(
        Map.entry("com.amazonaws.kms", "KmsException"),
        Map.entry("com.amazonaws.dynamodb", "DynamoDbException"),
        Map.entry("com.amazonaws.s3", "S3Exception")
      );
    // These short names are used for convince in docs and errors messages.
    AWS_SERVICE_NAMESPACE_TO_SHORT_NAME =
      Map.ofEntries(
        Map.entry("com.amazonaws.kms", "KMS"),
        Map.entry("com.amazonaws.dynamodb", "DDB"),
        Map.entry("com.amazonaws.s3", "S3")
      );
  }

  /** Validates that Polymorph knows non-smithy modeled constants for an AWS Service */
  private void checkForAwsServiceConstants() {
    String namespace = serviceShape.getId().getNamespace();
    checkForAwsServiceConstants(namespace);
  }

  /** Validates that Polymorph knows non-smithy modeled constants for an AWS Service */
  private static void checkForAwsServiceConstants(String namespace) {
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
    boolean knownShortName = AWS_SERVICE_NAMESPACE_TO_SHORT_NAME.containsKey(
      namespace
    );
    if (!knownShortName) {
      throw new IllegalArgumentException(
        "Polymorph does not know this service's short name: %s".formatted(
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

  public static ClassName classNameForServiceClient(ServiceShape shape) {
    String awsServiceSmithyNamespace = shape.toShapeId().getNamespace();
    checkForAwsServiceConstants(awsServiceSmithyNamespace);
    return ClassName.get(
      packageNameForAwsSdkV2Shape(shape),
      AWS_SERVICE_NAMESPACE_TO_CLIENT_INTERFACE.get(awsServiceSmithyNamespace)
    );
  }

  public static String shortNameForService(ServiceShape shape) {
    String awsServiceSmithyNamespace = shape.toShapeId().getNamespace();
    boolean knownShortName = AWS_SERVICE_NAMESPACE_TO_SHORT_NAME.containsKey(
      awsServiceSmithyNamespace
    );
    if (!knownShortName) {
      throw new IllegalArgumentException(
        "Polymorph does not know this service's short name: %s".formatted(
            awsServiceSmithyNamespace
          )
      );
    }
    return AWS_SERVICE_NAMESPACE_TO_SHORT_NAME.get(awsServiceSmithyNamespace);
  }

  /**
   * <p>In the AWS SDK Java V2,
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
      if (shapeRequiresTypeConversionFromStringToStructure(shapeId)) {
        return classForEnum(shape);
      }

      return classForString();
    }
    if (SHAPE_TYPES_LIST_SET_MAP.contains(shape.getType())) {
      return typeForListSetOrMapNoEnum(shapeId);
    }
    return typeForShape(shapeId);
  }

  @Override
  public TypeName typeForShape(final ShapeId shapeId) {
    final Shape shape = model.expectShape(shapeId);

    // Overrides BYTE shapeType type conversion to SdkBytes conversion.
    if (shape.getType().equals(ShapeType.BYTE)) {
      return JavaAwsSdkV2.BLOB_TO_NATIVE_SDK_BYTES;
    }

    // BinarySetAttributeValue is the only list of bytes
    if (shapeId.getName().contains("BinarySetAttributeValue")) {
      return ParameterizedTypeName.get(
        ClassName.get(List.class),
        JavaAwsSdkV2.BLOB_TO_NATIVE_SDK_BYTES
      );
    }

    return super.typeForShape(shapeId);
  }

  /**
   * Returns true if the provided ShapeId has type string in the Smithy model, but AWS SDK for
   *   Java V2 effectively expects type structure.
   * @param shapeId
   * @return true if AWS SDK for Java V2 expects this to have been modeled as a structure in Smithy
   */
  protected boolean shapeRequiresTypeConversionFromStringToStructure(
    ShapeId shapeId
  ) {
    return (
      shapeId
        .toString()
        .contains("com.amazonaws.kms#EncryptionAlgorithmSpec") ||
      shapeId.toString().contains("com.amazonaws.kms#SigningAlgorithmSpec") ||
      shapeId.toString().contains("com.amazonaws.kms#GrantOperation")
    );
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
        "typeForListSetOrMapNoEnum only accepts LIST, SET or MAP. Got: " +
        shape.getType() +
        " for ShapeId: " +
        shapeId
      );
    };
  }

  /**
   * Returns CodeBlock containing something like `member`.
   * Most AWS SDK V2 setters are `uncapitalizedMemberName` with edge cases in this function
   * @param shape
   * @return CodeBlock containing something like `member`.
   */
  public CodeBlock fieldForSetMember(MemberShape shape) {
    // Some strings have a token that requires multi-letter decapitalization (e.g. "SSE", "KMS")
    String tokenToUncapitalize = tokenToUncapitalizeInShape(shape);
    if (!tokenToUncapitalize.equals("")) {
      return CodeBlock.of(
        "$L",
        shape
          .getMemberName()
          .replace(tokenToUncapitalize, tokenToUncapitalize.toLowerCase())
      );
    }
    // Attributes of SDK AttributeValue shapes are always lower-case
    if (
      shape.getContainer().getName().equals("AttributeValue") &&
      isAttributeValueType(shape)
    ) {
      // "NULL" attribute is set using "nul"
      if (shape.getMemberName().equals("NULL")) {
        return CodeBlock.of("nul");
      }
      return CodeBlock.of("$L", shape.getMemberName().toLowerCase());
    }

    return CodeBlock.of("$L", uncapitalize(shape.getMemberName()));
  }

  public static ClassName classNameForAwsSdkShape(final Shape shape) {
    // Assume that the shape is in the model package
    ClassName smithyName = ClassName.get(
      defaultModelPackageName(packageNameForAwsSdkV2Shape(shape)),
      StringUtils.capitalize(shape.getId().getName())
    );

    if (smithyName.simpleName().endsWith("Input")) {
      return ClassName.get(
        smithyName.packageName(),
        smithyName
          .simpleName()
          .substring(0, smithyName.simpleName().lastIndexOf("Input")) +
        "Request"
      );
    }

    if (smithyName.simpleName().endsWith("Output")) {
      return ClassName.get(
        smithyName.packageName(),
        smithyName
          .simpleName()
          .substring(0, smithyName.simpleName().lastIndexOf("Output")) +
        "Response"
      );
    }

    if (shape.hasTrait(ErrorTrait.class)) {
      if (smithyName.simpleName().contains("KMS")) {
        return ClassName.get(
          smithyName.packageName(),
          smithyName.simpleName().replace("KMS", "Kms")
        );
      }
      if (smithyName.simpleName().contains("CMK")) {
        return ClassName.get(
          smithyName.packageName(),
          smithyName.simpleName().replace("CMK", "CmK")
        );
      }
      if (smithyName.simpleName().endsWith("InternalServerError")) {
        return ClassName.get(
          smithyName.packageName(),
          smithyName
            .simpleName()
            .replace("InternalServerError", "InternalServerErrorException")
        );
      }
      if (smithyName.simpleName().endsWith("RequestLimitExceeded")) {
        return ClassName.get(
          smithyName.packageName(),
          smithyName
            .simpleName()
            .replace("RequestLimitExceeded", "RequestLimitExceededException")
        );
      }
    }
    return smithyName;
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
    // check if this Shape is in AWS SDK for Java V2 package
    if (AwsSdkNameResolverHelpers.isInAwsSdkNamespace(shape.getId())) {
      AwsSdkNativeV2.classNameForAwsSdkShape(shape);
    }
    return super.classNameForStructure(shape);
  }

  public TypeName typeForOperationOutput(final ShapeId shapeId) {
    StructureShape shape = model.expectShape(shapeId, StructureShape.class);
    return classNameForStructure(shape);
  }

  public final String v2FormattedEnumValue(
    // ShapeIds are great; every method in this class SHOULD accept a ShapeId.
    // If we ever need to handle an exception to the enum naming pattern (which the AWS SDK is full of)
    // The ShapeId will be used.
    @SuppressWarnings("unused") final ShapeId shapeId,
    final String enumValueName
  ) {
    // TODO: We SHOULD employ the awsSDkNaming for more of the logic above..
    return this.awsSDKNaming.getEnumValueName(enumValueName);
  }

  /**
   * Returns the TypeName for an AWS Service's Client Interface.
   */
  @Override
  public ClassName classNameForService(final ServiceShape shape) {
    //TODO: refactor to not throw error on other namespace,
    // but instead check AWS_SERVICE_NAMESPACE_TO_CLIENT_INTERFACE for
    // namespace, and throw exception if not found.
    checkInServiceNamespace(shape.getId());
    return ClassName.get(
      packageName,
      AWS_SERVICE_NAMESPACE_TO_CLIENT_INTERFACE.get(
        serviceShape.getId().getNamespace()
      )
    );
  }

  /**
   * Returns the TypeName for an AWS Service's Base Exception.
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
    return "software.amazon.awssdk.services.%s".formatted(rtn);
  }

  static String packageNameForAwsSdkV2Shape(final Shape shape) {
    String awsServiceName = AwsSdkNameResolverHelpers.awsServiceNameFromShape(
      shape
    );
    return packageNameForService(awsServiceName);
  }

  public static String defaultModelPackageName(final String packageName) {
    return "%s.model".formatted(packageName);
  }
}
