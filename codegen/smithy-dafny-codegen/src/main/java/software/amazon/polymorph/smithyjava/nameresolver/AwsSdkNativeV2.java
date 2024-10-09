// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.nameresolver;

import static software.amazon.polymorph.smithyjava.nameresolver.AwsSdkV2NameResolverUtils.isAttributeValueType;
import static software.amazon.polymorph.smithyjava.nameresolver.AwsSdkV2NameResolverUtils.tokenToUncapitalizeInShape;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.SHAPE_TYPES_LIST_SET_MAP;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.ParameterizedTypeName;
import com.squareup.javapoet.TypeName;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import software.amazon.awssdk.codegen.internal.Utils;
import software.amazon.awssdk.codegen.model.service.ServiceModel;
import software.amazon.awssdk.codegen.naming.DefaultNamingStrategy;
import software.amazon.awssdk.utils.internal.CodegenNamingUtils;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.polymorph.smithyjava.generator.awssdk.v2.JavaAwsSdkV2;
import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.knowledge.OperationIndex;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ShapeType;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.TitleTrait;
import software.amazon.smithy.model.traits.TraitDefinition;
import software.amazon.smithy.utils.StringUtils;

/**
 * There are certain assumptions we can/have to make about
 * Types from the AWS SDK for Java V2 libraries.
 */
public class AwsSdkNativeV2 extends Native {

  private final DefaultNamingStrategy awsSDKNaming;
  private final OperationIndex operationIndex;

  public AwsSdkNativeV2(final ServiceShape serviceShape, final Model model) {
    super(
      packageNameForAwsSdkV2Shape(serviceShape),
      serviceShape,
      model,
      defaultModelPackageName(packageNameForAwsSdkV2Shape(serviceShape)),
      CodegenSubject.AwsSdkVersion.V2
    );
    awsSDKNaming = new DefaultNamingStrategy(new ServiceModel(), null);
    operationIndex = new OperationIndex(model);
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
    return ClassName.get(
      packageNameForAwsSdkV2Shape(shape),
      AWS_SERVICE_NAMESPACE_TO_CLIENT_INTERFACE.getOrDefault(
        awsServiceSmithyNamespace,
        sdkId(shape) + "Client"
      )
    );
  }

  public static String titleForService(ServiceShape shape) {
    Optional<TitleTrait> maybeTrait = shape.getTrait(TitleTrait.class);
    return maybeTrait.isPresent() ? maybeTrait.get().getValue() : "AWS";
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
      return classForEnum(shape);
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

    return CodeBlock.of("$L", Utils.unCapitalize(shape.getMemberName()));
  }

  public ClassName classNameForAwsSdkShape(final Shape shape) {
    // Assume that the shape is in the model package
    ClassName smithyName = ClassName.get(
      defaultModelPackageName(packageNameForAwsSdkV2Shape(shape)),
      StringUtils.capitalize(shape.getId().getName())
    );

    if (operationIndex.isInputStructure(shape)) {
      var operations = operationIndex.getInputBindings(shape);
      if (operations.size() > 1) {
        throw new IllegalArgumentException(
          "Structures bound to more than one operation as input are not supported: " +
          shape
        );
      }
      var operation = operations.stream().findFirst().get();
      return ClassName.get(
        smithyName.packageName(),
        CodegenNamingUtils.pascalCase(operation.getId().getName()) + "Request"
      );
    }

    if (operationIndex.isOutputStructure(shape)) {
      var operations = operationIndex.getOutputBindings(shape);
      if (operations.size() > 1) {
        throw new IllegalArgumentException(
          "Structures bound to more than one operation as output are not supported: " +
          shape
        );
      }
      var operation = operations.stream().findFirst().get();
      return ClassName.get(
        smithyName.packageName(),
        CodegenNamingUtils.pascalCase(operation.getId().getName()) + "Response"
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
      return classNameForAwsSdkShape(shape);
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

  private static String sdkId(ServiceShape serviceShape) {
    return serviceShape
      .getTrait(ServiceTrait.class)
      .map(serviceTrait -> serviceTrait.getSdkId())
      .orElse(serviceShape.getId().getName());
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
      AWS_SERVICE_NAMESPACE_TO_CLIENT_INTERFACE.getOrDefault(
        serviceShape.getId().getNamespace(),
        sdkId(serviceShape) + "Client"
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
      AWS_SERVICE_NAMESPACE_TO_BASE_EXCEPTION.getOrDefault(
        serviceShape.getId().getNamespace(),
        sdkId(serviceShape) + "Exception"
      )
    );
  }

  public static String packageNameForService(final String awsServiceName) {
    String rtn = awsServiceName;
    return "software.amazon.awssdk.services.%s".formatted(rtn);
  }

  public static String packageNameForAwsSdkV2Shape(final Shape shape) {
    String awsServiceName = AwsSdkNameResolverHelpers.awsServiceNameFromShape(
      shape
    );
    return packageNameForService(awsServiceName);
  }

  public static String defaultModelPackageName(final String packageName) {
    return "%s.model".formatted(packageName);
  }
}
