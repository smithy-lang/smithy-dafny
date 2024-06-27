// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava;

import static software.amazon.polymorph.smithyjava.generator.Generator.NATIVE_VAR;

import java.util.List;
import java.util.Objects;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import software.amazon.awssdk.utils.Pair;
import software.amazon.awssdk.utils.StringUtils;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.Shape;

/**
 * @param desc    JavaDoc Body content
 * @param params  List of {@link Pair} of Strings which will get {@code @param}
 * @param returns String which will get {@code @return}
 */
public record OperationJavaDoc(
  @Nullable String desc,
  @Nullable List<Pair<String, String>> params,
  @Nullable String returns
) {
  static final String LF = System.lineSeparator();

  public String getDoc() {
    // Note: this is largely copied from another AWS Product:
    // https://github.com/aws/aws-sdk-java-v2/blob/79b34ed72b2d39084e3c2b516d150f89b6bf39f8/codegen/src/main/java/software/amazon/awssdk/codegen/docs/DocumentationBuilder.java#L215
    StringBuilder str = new StringBuilder();
    if (StringUtils.isNotBlank(desc)) {
      str.append(desc).append(LF);
    }
    if (Objects.nonNull(params)) {
      str.append(LF);
      params.forEach(p ->
        p.apply((paramName, paramDoc) -> formatParam(str, paramName, paramDoc))
      );
    }
    if (StringUtils.isNotBlank(returns)) {
      str.append("@return ").append(returns);
    }
    return str.append(LF).toString();
  }

  private StringBuilder formatParam(
    StringBuilder doc,
    String paramName,
    String paramDoc
  ) {
    if (StringUtils.isNotBlank(paramDoc)) {
      return doc
        .append("@param ")
        .append(paramName)
        .append(" ")
        .append(paramDoc)
        .append(LF);
    }
    return doc;
  }

  public static OperationJavaDoc fromOperationShape(
    Model model,
    OperationShape shape
  ) {
    Shape inputShape = model.expectShape(shape.getInputShape());
    @Nullable
    String paramDoc = ModelUtils
      .getDocumentationOrJavadoc(inputShape)
      .orElse(null);
    @Nonnull
    String paramName = NATIVE_VAR;
    Shape outputShape = model.expectShape(shape.getOutputShape());
    @Nullable
    String returns = ModelUtils
      .getDocumentationOrJavadoc(outputShape)
      .orElse(null);
    @Nullable
    String desc = ModelUtils.getDocumentationOrJavadoc(shape).orElse(null);
    List<Pair<String, String>> params = StringUtils.isNotBlank(paramDoc)
      ? List.of(Pair.of(paramName, paramDoc))
      : null;
    return new OperationJavaDoc(desc, params, returns);
  }
}
