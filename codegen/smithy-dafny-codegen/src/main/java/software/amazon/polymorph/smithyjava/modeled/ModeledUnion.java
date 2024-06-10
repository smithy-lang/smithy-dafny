// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.modeled;

import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import java.util.List;
import java.util.Objects;
import javax.lang.model.element.Modifier;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.smithy.model.shapes.UnionShape;

public class ModeledUnion {

  public static final String UNION_VALIDATE_METHOD_NAME = "onlyOneNonNull";
  private static final String ALL_FIELDS_VAR = "allValues";

  /**
   * If and only if one entry of {@code ALL_FIELDS_VAR} is non-null,
   * return {@code true}.
   * Otherwise, return {@code false}.<p>
   * See <a href="https://github.com/aws/aws-s3-encryption-client-java/blob/d0bcd38efb589d72f04f2aeae721de4a974718bd/src/main/java/software/amazon/encryption/s3/S3EncryptionClient.java#L223-L236">...</a>
   * @author Sean Swezey<p>
   */
  @SuppressWarnings("JavadocDeclaration")
  private static final CodeBlock ONLY_ONE_NON_NULL = CodeBlock
    .builder()
    .addStatement("boolean haveOneNonNull = false")
    .beginControlFlow("for (Object o : $L)", ALL_FIELDS_VAR)
    .beginControlFlow("if ($T.nonNull(o))", Objects.class)
    .beginControlFlow("if (haveOneNonNull)")
    .addStatement("return false")
    .endControlFlow()
    .addStatement("haveOneNonNull = true")
    .endControlFlow()
    .endControlFlow()
    .addStatement("return haveOneNonNull")
    .build();

  public static JavaFile javaFile(
    String packageName,
    UnionShape shape,
    JavaLibrary subject
  ) {
    return ModeledStructure.javaFile(packageName, shape, subject);
  }

  /** Aggregates all fields into {@code ALL_FIELDS_VAR} and then {@code ONLY_ONE_NON_NULL} */
  protected static MethodSpec unionValidate(UnionShape shape) {
    List<CodeBlock> thisAllFields = shape
      .members()
      .stream()
      .map(member -> CodeBlock.of("this.$L", member.getMemberName()))
      .toList();
    return MethodSpec
      .methodBuilder(UNION_VALIDATE_METHOD_NAME)
      .returns(boolean.class)
      .addModifiers(Modifier.PRIVATE)
      .addStatement(
        "$T[] $L = {$L}",
        Object.class,
        ALL_FIELDS_VAR,
        CodeBlock.join(thisAllFields, ", ")
      )
      .addCode(ONLY_ONE_NON_NULL)
      .build();
  }
}
