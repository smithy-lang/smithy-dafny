// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.nameresolver;

import static software.amazon.smithy.utils.StringUtils.capitalize;
import static software.amazon.smithy.utils.StringUtils.uncapitalize;

import com.google.common.base.CaseFormat;
import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.TypeName;
import software.amazon.awssdk.codegen.internal.Utils;
import software.amazon.awssdk.utils.internal.CodegenNamingUtils;
import software.amazon.polymorph.smithydafny.DafnyNameResolver;
import software.amazon.polymorph.smithydafny.DafnyVersion;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
import software.amazon.polymorph.utils.DafnyNameResolverHelpers;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.utils.StringUtils;

public class AwsSdkDafnyV2 extends Dafny {

  public AwsSdkDafnyV2(
    ServiceShape serviceShape,
    Model model,
    DafnyVersion dafnyVersion
  ) {
    super(
      packageNameForServiceShape(serviceShape),
      model,
      serviceShape,
      CodegenSubject.AwsSdkVersion.V2,
      dafnyVersion
    );
  }

  @Override
  ClassName classNameForService(ServiceShape shape) {
    if (AwsSdkNameResolverHelpers.isInAwsSdkNamespace(shape.getId())) {
      return classNameForAwsService(shape);
    }
    return super.classNameForService(shape);
  }

  public static ClassName classNameForAwsService(ServiceShape shape) {
    return ClassName.get(
      modelPackageNameForNamespace(shape.getId().getNamespace()),
      DafnyNameResolverHelpers.dafnyCompilesExtra_(
        DafnyNameResolver.traitNameForServiceClient(shape)
      )
    );
  }

  @Override
  ClassName classNameForResource(ResourceShape shape) {
    if (AwsSdkNameResolverHelpers.isInAwsSdkNamespace(shape.getId())) {
      return ClassName.get(
        modelPackageNameForNamespace(shape.getId().getNamespace()),
        "I%s".formatted(StringUtils.capitalize(shape.getId().getName()))
      );
    }
    return super.classNameForResource(shape);
  }

  /**
   * Returns CodeBlock containing something like `variable.member()`.
   * Most AWS SDK V2 getters are `uncapitalizedMemberName()` with edge cases in this function
   * @param variableName variable to get member from
   * @param memberShape member to retrieve from variable
   * @return CodeBlock containing something like `variable.member()`.
   */
  public CodeBlock methodForGetMember(
    CodeBlock variableName,
    MemberShape memberShape
  ) {
    // Some Strings have a token that requires multi-letter decapitalization (e.g. "SSE", "KMS")
    String tokenToUncapitalize =
      AwsSdkV2NameResolverUtils.tokenToUncapitalizeInShape(memberShape);
    if (!tokenToUncapitalize.equals("")) {
      return CodeBlock.of(
        "$L.$L()",
        variableName,
        memberShape
          .getMemberName()
          .replace(tokenToUncapitalize, tokenToUncapitalize.toLowerCase())
      );
    }

    // Message: Exception message. Retrieved via `getMessage()`.
    if (
      "message".equals(uncapitalize(memberShape.getMemberName())) &&
      model.expectShape(memberShape.getContainer()).hasTrait(ErrorTrait.class)
    ) {
      return CodeBlock.of(
        "$L.get$L()",
        variableName,
        capitalize(memberShape.getMemberName())
      );
    }

    // Attributes of SDK AttributeValue shapes are entirely lower-case
    if (AwsSdkV2NameResolverUtils.isAttributeValueType(memberShape)) {
      // "NULL" attribute is retrieved using "nul"
      if (memberShape.getMemberName().equals("NULL")) {
        return CodeBlock.of("$L.nul()", variableName);
      }
      return CodeBlock.of(
        "$L.$L()",
        variableName,
        memberShape.getMemberName().toLowerCase()
      );
    }

    return CodeBlock.of(
      "$L.$L()",
      variableName,
      Utils.unCapitalize(memberShape.getMemberName())
    );
  }

  /**
   * Formats enum name for AWS SDK V2 if name requires reformatting to match Smithy model
   * @param dafnyEnumType Smithy-defined and formatted enum type
   * @param enumValue
   * @return If enum requires formatting to match the Smithy model: reformatted enum name
   *         else: unchanged name
   */
  public String formatEnumCaseName(
    final TypeName dafnyEnumType,
    final String enumValue
  ) {
    if (enumValue.equals("ECC_SECG_P256K1")) {
      return "ECC_SECG_P256_K1";
    }

    return enumRequiresUpperCamelcaseConversion(dafnyEnumType.toString())
      ? CaseFormat.UPPER_CAMEL.to(CaseFormat.UPPER_UNDERSCORE, enumValue)
      : enumValue;
  }

  /**
   * Returns trye if values for this enum type require conversion to UpperCamelcase.
   * AWS SDK V2 defines values for these enum types as UPPER_UNDERSCORE_FORMATTED.
   * The Smithy-defined model has these values UpperCamelcaseFormatted.
   * @param dafnyEnumType Smithy-defined and formatted enum type
   * @return trye if values for dafnyEnumType require conversion to UpperCamelcase.
   */
  protected boolean enumRequiresUpperCamelcaseConversion(
    final String dafnyEnumType
  ) {
    return (
      dafnyEnumType.equals(
        "software.amazon.cryptography.services.kms.internaldafny.types.KeyState"
      ) ||
      dafnyEnumType.equals(
        "software.amazon.cryptography.services.kms.internaldafny.types.GrantOperation"
      ) ||
      dafnyEnumType.equals(
        "software.amazon.cryptography.services.dynamodb.internaldafny.types.BatchStatementErrorCodeEnum"
      )
    );
  }

  /**
   * Wrapper around Dafny.getMemberFieldValue.
   * Checks if shape is a DynamoDB attribute value type:
   *  - If it is, it doesn't need .dtor_value(); use getMemberField
   *  - If it isn't, it needs .dtor_value(); use getMemberFieldValue
   * @param shape
   * @return CodeBlock to get member field for SDK V2 shape
   */
  public static CodeBlock getV2MemberFieldValue(MemberShape shape) {
    if (AwsSdkV2NameResolverUtils.isAttributeValueType(shape)) {
      return getMemberField(shape);
    }
    return Dafny.getMemberFieldValue(shape);
  }

  @Override
  public CodeBlock typeDescriptor(ShapeId shapeId) {
    if (shapeIdRequiresStaticTypeDescriptor(shapeId)) {
      // Explicitly assigning this string is reasonable because these 2 classes assign the
      //     same types.
      // Extend this assignment if we find more shapes that don't get classes generated
      //     require special typeDescriptors.
      return CodeBlock.of(
        "TypeDescriptor.referenceWithInitializer(dafny.DafnyMap.class, () -> dafny.DafnyMap.<dafny.DafnySequence<? extends Character>,AttributeValue> empty())"
      );
    }
    return super.typeDescriptor(shapeId);
  }

  /**
   * AttributeMap and Key require special conversion.
   * These are unique; they are the two map types used in generated code that do not have an
   *     associated Dafny-generated type Java class.
   * When Dafny compiles map types into Java, Dafny will not generate a Java class for a map
   *     if the Dafny type does not have a predicate.
   * Some maps are modelled to have a bound on the number of key/value pairs in the map.
   *     Polymorph translates these as a Dafny predicate. These 2 classes do not have a bound
   *     on map size, so they don't have a predicate, and aren't compiled into classes.
   * Only classes have a _typeDescriptor() method; these are not classes, so they don't have one.
   * Below, Polymorph generates a likeness of the _typeDescriptor() method for these types.
   * Note that this results in an "unchecked cast" compiler warning, but the Dafny-generated
   *     cast also produces this warning.
   * If we find more shapes that match this criteria, we should extend this logic.
   * @param shapeId
   * @return
   */
  public boolean shapeIdRequiresStaticTypeDescriptor(final ShapeId shapeId) {
    String className = classForNotErrorNotUnitShape(shapeId).toString();

    return (
      className.equals(
        "software.amazon.cryptography.services.dynamodb.internaldafny.types.AttributeMap"
      ) ||
      className.equals(
        "software.amazon.cryptography.services.dynamodb.internaldafny.types.Key"
      )
    );
  }
}
