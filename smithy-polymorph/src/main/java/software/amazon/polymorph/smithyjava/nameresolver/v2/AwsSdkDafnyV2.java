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
        // Message: Exception message. Retrieved via `getMessage()`.
        if ("message".equals(uncapitalize(memberShape.getMemberName()))) {
            return CodeBlock.of("$L.get$L()", variableName, capitalize(memberShape.getMemberName()));
        }
        return CodeBlock.of("$L.$L()", variableName, uncapitalize(memberShape.getMemberName()));
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
            || dafnyEnumType.equals("Dafny.Com.Amazonaws.Kms.Types.GrantOperation");
    }
}
