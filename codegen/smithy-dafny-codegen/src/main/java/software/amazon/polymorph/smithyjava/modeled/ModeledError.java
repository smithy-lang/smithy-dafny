// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.modeled;

import static javax.lang.model.element.Modifier.FINAL;
import static javax.lang.model.element.Modifier.PRIVATE;
import static javax.lang.model.element.Modifier.PROTECTED;
import static software.amazon.polymorph.smithyjava.modeled.ModeledStructure.getterMethod;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeSpec;
import java.util.Collections;
import java.util.List;
import javax.lang.model.element.Modifier;
import software.amazon.polymorph.smithyjava.BuildMethod;
import software.amazon.polymorph.smithyjava.BuilderMemberSpec;
import software.amazon.polymorph.smithyjava.BuilderSpecs;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.polymorph.smithyjava.unmodeled.ErrorHelpers;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.shapes.StructureShape;

public class ModeledError {

  public static JavaFile javaFile(
    String packageName,
    StructureShape shape,
    JavaLibrary subject
  ) {
    ClassName className = ClassName.get(packageName, shape.getId().getName());
    ClassName superName = ClassName.get(RuntimeException.class);
    // Fields in the Smithy Model
    List<BuilderMemberSpec> modelFields = BuilderSpecs.shapeToArgs(
      shape,
      subject
    );
    // Union of Fields in (Smithy Model) + (THROWABLE_ARGS)
    List<BuilderMemberSpec> allFields = ErrorHelpers.prependThrowableArgs(
      modelFields
    );
    // Fields in (Smithy Model) NOT IN (THROWABLE_ARGS)
    List<BuilderMemberSpec> localOnlyFields = ErrorHelpers.removeThrowableArgs(
      modelFields
    );
    final boolean overrideSuperFalse = false;
    BuilderSpecs builderSpecs = new BuilderSpecs(
      className,
      null,
      allFields,
      Collections.emptyList()
    );
    TypeSpec.Builder spec = TypeSpec
      .classBuilder(className)
      .addModifiers(Modifier.PUBLIC)
      .superclass(superName);
    ModelUtils.getDocumentationOrJavadoc(shape).map(spec::addJavadoc);
    localOnlyFields.forEach(field -> {
      // Add local fields
      spec.addField(field.toFieldSpec(PRIVATE, FINAL));
    });
    spec.addMethod(ErrorHelpers.messageFromBuilder(builderSpecs));
    // Add getter methods
    spec.addMethods(ErrorHelpers.throwableGetters());
    localOnlyFields.forEach(field -> spec.addMethod(getterMethod(field)));
    spec
      .addType(builderSpecs.builderInterface())
      .addType(
        builderSpecs.builderImpl(
          overrideSuperFalse,
          builderSpecs.implModelConstructor(),
          BuildMethod.implBuildMethod(
            overrideSuperFalse,
            shape,
            subject,
            packageName
          )
        )
      );

    spec
      .addMethod(constructor(builderSpecs, localOnlyFields))
      .addMethod(builderSpecs.toBuilderMethod(overrideSuperFalse))
      .addMethod(builderSpecs.builderMethod());

    return JavaFile
      .builder(packageName, spec.build())
      .skipJavaLangImports(true)
      .build();
  }

  private static MethodSpec constructor(
    BuilderSpecs builderSpecs,
    List<BuilderMemberSpec> localOnlyFields
  ) {
    MethodSpec.Builder method = MethodSpec
      .constructorBuilder()
      .addModifiers(PROTECTED)
      .addParameter(builderSpecs.builderImplName(), BuilderSpecs.BUILDER_VAR)
      .addStatement(
        "super(messageFromBuilder($L), $L.cause())",
        BuilderSpecs.BUILDER_VAR,
        BuilderSpecs.BUILDER_VAR
      );
    localOnlyFields.forEach(field ->
      method.addStatement(
        "this.$L = $L.$L()",
        field.name,
        BuilderSpecs.BUILDER_VAR,
        field.name
      )
    );
    return method.build();
  }
}
