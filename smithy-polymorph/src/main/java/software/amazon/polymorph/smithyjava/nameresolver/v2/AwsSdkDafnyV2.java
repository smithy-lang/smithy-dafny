package software.amazon.polymorph.smithyjava.nameresolver;

import com.google.common.base.CaseFormat;
import com.squareup.javapoet.ClassName;

import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.TypeName;
import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.utils.StringUtils;

import static software.amazon.polymorph.smithydafny.DafnyNameResolver.traitNameForServiceClient;
import static software.amazon.smithy.utils.StringUtils.capitalize;
import static software.amazon.smithy.utils.StringUtils.uncapitalize;

public class AwsSdkDafnyV2 extends Dafny {

    public AwsSdkDafnyV2(ServiceShape serviceShape, Model model) {
        super(packageNameForServiceShape(serviceShape), model, serviceShape);
    }

    @Override
    ClassName classNameForService(ServiceShape shape) {
        if (AwsSdkNameResolverHelpers.isAwsSdkServiceId(shape.getId())) {
            return ClassName.get(
                    modelPackageNameForNamespace(shape.getId().getNamespace()),
                    traitNameForServiceClient(shape)
            );
        }
        return super.classNameForService(shape);
    }

    @Override
    ClassName classNameForResource(ResourceShape shape) {
        if (AwsSdkNameResolverHelpers.isAwsSdkServiceId(shape.getId())) {
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
    public CodeBlock methodForGetMember(CodeBlock variableName, MemberShape memberShape) {
        // AWS Account ID: Uncapitalize all of `AWS` --> `aws`
        if ("AWSAccountId".equals(memberShape.getMemberName())) {
            return CodeBlock.of("$L.awsAccountId()", variableName);
        }

        // SSE (secure-side encryption) Description: Uncapitalize all of `SSE` --> `sse`
        // TODO: Refactor with SSE renaming logic in AwsSdkNativeV2
        if (memberShape.getMemberName().startsWith("SSE")) {
            String suffix = memberShape.getMemberName()
                .substring(memberShape.getMemberName().lastIndexOf("SSE") + "SSE".length());
            return CodeBlock.of("$L.sse$L()", variableName, suffix);
        }

        // TODO: Refactor with KMS renaming logic in AwsSdkNativeV2
        if (memberShape.getMemberName().startsWith("KMS")) {
            String suffix = memberShape.getMemberName()
                .substring(memberShape.getMemberName().lastIndexOf("KMS") + "KMS".length());
            return CodeBlock.of("$L.kms$L()", variableName, suffix);
        }

        // Message: Exception message. Retrieved via `getMessage()`.
        if ("message".equals(uncapitalize(memberShape.getMemberName()))) {
            // BatchStatementError and CancellationReason types' messages are retrieved via "message".
            if (memberShape.getContainer().getName().contains("BatchStatementError")
                    || memberShape.getContainer().getName().contains("CancellationReason")) {
                return CodeBlock.of("$L.$L()", variableName,
                    uncapitalize(memberShape.getMemberName()));
            } else {
                return CodeBlock.of("$L.get$L()", variableName,
                    capitalize(memberShape.getMemberName()));
            }
        }

        // Attributes of SDK AttributeValue shapes are entirely lower-case
        if (isAttributeValueType(memberShape)) {
            // "NULL" attribute is retrieved using "nul"
            if (memberShape.getMemberName().equals("NULL")) {
                return CodeBlock.of("$L.nul()", variableName);
            }
            return CodeBlock.of("$L.$L()", variableName, memberShape.getMemberName().toLowerCase());
        }

        return CodeBlock.of("$L.$L()", variableName, uncapitalize(memberShape.getMemberName()));
    }

    /**
     * Returns true if shape is an attribute of an AttributeValue shape; false otherwise
     * @param shape
     * @return true if shape is an attribute of an AttributeValue shape; false otherwise
     */
    protected static boolean isAttributeValueType(MemberShape shape) {
        shape.getContainer().getName().equals("AttributeValue");
        String memberName = shape.getMemberName();
        return (shape.getContainer().getName().equals("AttributeValue")
            && (memberName.equals("BOOL")
                || memberName.equals("NULL")
                || memberName.equals("L")
                || memberName.equals("M")
                || memberName.equals("BS")
                || memberName.equals("NS")
                || memberName.equals("SS")
                || memberName.equals("B")
                || memberName.equals("N")
                || memberName.equals("S")
            ));
    }

    /**
     * Formats enum name for AWS SDK V2 if name requires reformatting to match Smithy model
     * @param dafnyEnumType Smithy-defined and formatted enum type
     * @param enumValue
     * @return If enum requires formatting to match the Smithy model: reformatted enum name
     *         else: unchanged name
     */
    public String formatEnumCaseName(final TypeName dafnyEnumType, final String enumValue) {
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
    protected boolean enumRequiresUpperCamelcaseConversion(final String dafnyEnumType) {
        return dafnyEnumType.equals("Dafny.Com.Amazonaws.Kms.Types.KeyState")
            || dafnyEnumType.equals("Dafny.Com.Amazonaws.Kms.Types.GrantOperation")
            || dafnyEnumType.equals("Dafny.Com.Amazonaws.Dynamodb.Types.BatchStatementErrorCodeEnum");
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
        if (isAttributeValueType(shape)) {
            return getMemberField(shape);
        }
        return Dafny.getMemberFieldValue(shape);
    }

    @Override
    public CodeBlock typeDescriptor(ShapeId shapeId) {

        if (shapeIdRequiresStaticTypeDescriptor(shapeId)) {
            // TODO: Extend this assignment if we find more shapes that don't get classes generated.
            //   However, explicitly assigning this string works for these 2 classes.
            return CodeBlock.
                of("TypeDescriptor.referenceWithInitializer(dafny.DafnyMap.class, () -> dafny.DafnyMap.<dafny.DafnySequence<? extends Character>,AttributeValue> empty())");
        }
        return super.typeDescriptor(shapeId);
    }

    /**
     * AttributeMap and Key require special conversion.
     * These are unique; they are the two map types used in generated code that do not have an
     * associated Dafny-generated type Java class.
     * When Dafny compiles map types into Java, Dafny will not generate a Java class for a map
     * if the Dafny type does not have a predicate.
     * Some maps are modelled to have a bound on the number of key/value pairs in the map.
     * Polymorph translates these as a Dafny predicate. These 2 classes do not have a bound
     * on map size, so they don't have a predicate, and aren't compiled into classes.
     * Only classes have a _typeDescriptor() method; these are not classes, so they don't have one.
     * Below, Polymorph generates a likeness of the _typeDescriptor() method for these types.
     * Note that this results in an "unchecked cast" compiler warning, but the Dafny-generated
     * cast also produces this warning.
     * If we find more shapes that match this criteria, we should extend this logic.
     * @param shapeId
     * @return
     */
    public boolean shapeIdRequiresStaticTypeDescriptor(final ShapeId shapeId) {
        String className = classForNotErrorNotUnitShape(shapeId).toString();

        return (className.equals("AttributeMap")
            || className.equals("Key"));
    }
}
