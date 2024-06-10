// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.unmodeled;

import static javax.lang.model.element.Modifier.PRIVATE;
import static javax.lang.model.element.Modifier.PUBLIC;
import static javax.lang.model.element.Modifier.STATIC;
import static software.amazon.polymorph.smithyjava.BuilderMemberSpec.THROWABLE_ARGS;
import static software.amazon.smithy.utils.StringUtils.capitalize;

import com.squareup.javapoet.MethodSpec;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import software.amazon.polymorph.smithyjava.BuilderMemberSpec;
import software.amazon.polymorph.smithyjava.BuilderSpecs;

/**
 * ErrorHelpers holds static methods for generating Error shapes.
 */
public class ErrorHelpers {

  private static final Set<String> _THROWABLE_ARG_NAMES = THROWABLE_ARGS
    .stream()
    .map(field -> field.name)
    .collect(Collectors.toSet());

  /**
   * @return MethodSpec that checks the message field and cause's
   * message field for a valid message.
   */
  public static MethodSpec messageFromBuilder(BuilderSpecs builderSpecs) {
    return MethodSpec
      .methodBuilder("messageFromBuilder")
      .returns(String.class)
      .addModifiers(PRIVATE, STATIC)
      .addParameter(
        builderSpecs.builderInterfaceName(),
        BuilderSpecs.BUILDER_VAR
      )
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
  public static Iterable<MethodSpec> throwableGetters() {
    //noinspection DataFlowIssue (All THROWABLE_ARGS hava a JavaDoc)
    return THROWABLE_ARGS
      .stream()
      .map(field ->
        MethodSpec
          .methodBuilder(field.name)
          .returns(field.type)
          .addModifiers(PUBLIC)
          .addJavadoc(
            "See {@link $T#$L()}.",
            Throwable.class,
            String.format("get%s", capitalize(field.name))
          )
          .addStatement(
            "return this.$L()",
            String.format("get%s", capitalize(field.name))
          )
          .build()
      )
      .collect(Collectors.toList());
  }

  /** All Error Shapes MUST HAVE the THROWABLE_ARGS.
   * Their Model MAY already include these as Members.
   * This method ensures THROWABLE_ARGS are present only once
   * in an Error class. */
  public static List<BuilderMemberSpec> prependThrowableArgs(
    List<BuilderMemberSpec> originalArgs
  ) {
    List<BuilderMemberSpec> rtn = new ArrayList<>(
      THROWABLE_ARGS.size() + originalArgs.size()
    );
    rtn.addAll(THROWABLE_ARGS);
    originalArgs
      .stream()
      .filter(field -> !_THROWABLE_ARG_NAMES.contains(field.name))
      .forEach(rtn::add);
    return rtn;
  }

  public static List<BuilderMemberSpec> removeThrowableArgs(
    List<BuilderMemberSpec> originalArgs
  ) {
    List<BuilderMemberSpec> rtn = new ArrayList<>(originalArgs.size());
    originalArgs
      .stream()
      .filter(field -> !_THROWABLE_ARG_NAMES.contains(field.name))
      .forEach(rtn::add);
    return rtn;
  }
}
