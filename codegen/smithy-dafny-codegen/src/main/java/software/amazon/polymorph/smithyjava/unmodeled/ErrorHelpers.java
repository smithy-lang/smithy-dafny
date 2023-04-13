package software.amazon.polymorph.smithyjava.unmodeled;

import com.squareup.javapoet.MethodSpec;

import java.util.stream.Collectors;

import software.amazon.polymorph.smithyjava.BuilderMemberSpec;
import software.amazon.polymorph.smithyjava.BuilderSpecs;

import static javax.lang.model.element.Modifier.PRIVATE;
import static javax.lang.model.element.Modifier.PUBLIC;
import static javax.lang.model.element.Modifier.STATIC;
import static software.amazon.smithy.utils.StringUtils.capitalize;

/**
 * ErrorHelpers holds static methods for generating Error shapes.
 */
public class ErrorHelpers {
    /**
     * @return MethodSpec that checks the message field and cause's
     * message field for a valid message.
     */
    static MethodSpec messageFromBuilder(BuilderSpecs builderSpecs) {
        return MethodSpec.methodBuilder("messageFromBuilder")
                .returns(String.class)
                .addModifiers(PRIVATE, STATIC)
                .addParameter(builderSpecs.builderInterfaceName(), BuilderSpecs.BUILDER_VAR)
                .beginControlFlow("if ($L.message() != null)", BuilderSpecs.BUILDER_VAR)
                .addStatement("return $L.message()", BuilderSpecs.BUILDER_VAR)
                .endControlFlow()
                .beginControlFlow("if ($L.cause() != null)", BuilderSpecs.BUILDER_VAR)
                .addStatement("return $L.cause().getMessage()", BuilderSpecs.BUILDER_VAR)
                .endControlFlow()
                .addStatement("return null")
                .build();
    }

    /**
     * RuntimeException's fields are retrieved by `get + capitalize-field-name`,
     * but our generated Java just uses the field name.
     */
    static Iterable<MethodSpec> throwableGetters() {
        return BuilderMemberSpec.THROWABLE_ARGS.stream().map(field ->
                MethodSpec.methodBuilder(field.name)
                        .returns(field.type)
                        .addModifiers(PUBLIC)
                        .addStatement("return this.$L()",
                                String.format("get%s", capitalize(field.name)))
                        .build()).collect(Collectors.toList());
    }
}
