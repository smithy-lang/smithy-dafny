// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.unmodeled;

import static javax.lang.model.element.Modifier.FINAL;
import static javax.lang.model.element.Modifier.PRIVATE;
import static javax.lang.model.element.Modifier.PROTECTED;
import static javax.lang.model.element.Modifier.PUBLIC;
import static software.amazon.polymorph.smithyjava.BuilderMemberSpec.OPAQUE_ARGS;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.FieldSpec;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeName;
import com.squareup.javapoet.TypeSpec;
import java.util.Collections;
import java.util.List;
import javax.annotation.Nonnull;
import software.amazon.polymorph.smithyjava.BuilderMemberSpec;
import software.amazon.polymorph.smithyjava.BuilderSpecs;
import software.amazon.polymorph.smithyjava.modeled.ModeledStructure;

/**
 * OpaqueError is a Native-Java allegory to smithy-dafny's
 * {@code datatype Error}'s {@code Opaque(obj: object)} constructor<p>
 * There is no Smithy Shape for this.<p>
 */
public class OpaqueError {

  public static final String OPAQUE_ERROR = "OpaqueError";

  /** The class name of a module's Opaque Error. */
  public static ClassName nativeClassName(String packageName) {
    return ClassName.get(packageName, OPAQUE_ERROR);
  }

  /** A JavaFile containing the OpaqueError class definition. */
  public static JavaFile javaFile(String packageName) {
    ClassName className = nativeClassName(packageName);
    ClassName superName = ClassName.get(RuntimeException.class);
    List<BuilderMemberSpec> localOnlyFields = ErrorHelpers.removeThrowableArgs(
      OPAQUE_ARGS
    );
    BuilderSpecs builderSpecs = new BuilderSpecs(
      className,
      null,
      OPAQUE_ARGS,
      Collections.emptyList()
    );
    final boolean overrideSuperFalse = false;

    TypeSpec.Builder spec = TypeSpec
      .classBuilder(className)
      .addModifiers(PUBLIC)
      .superclass(superName);
    localOnlyFields.forEach(field -> {
      // Add local fields
      spec.addField(field.toFieldSpec(PRIVATE, FINAL));
    });
    spec.addMethod(ErrorHelpers.messageFromBuilder(builderSpecs));
    spec.addMethods(ErrorHelpers.throwableGetters());
    localOnlyFields.forEach(field ->
      spec.addMethod(ModeledStructure.getterMethod(field))
    );
    spec
      .addType(builderSpecs.builderInterface())
      .addType(
        builderSpecs.builderImpl(
          overrideSuperFalse,
          builderImplConstructor(packageName),
          implBuildMethod(className)
        )
      )
      .addMethod(constructor(builderSpecs))
      .addMethod(builderSpecs.toBuilderMethod(overrideSuperFalse))
      .addMethod(builderSpecs.builderMethod());

    return JavaFile
      .builder(packageName, spec.build())
      .skipJavaLangImports(true)
      .build();
  }

  /** The Class's constructor.*/
  static MethodSpec constructor(BuilderSpecs builderSpecs) {
    MethodSpec.Builder method = MethodSpec
      .constructorBuilder()
      .addModifiers(PROTECTED)
      .addParameter(builderSpecs.builderImplName(), BuilderSpecs.BUILDER_VAR)
      .addStatement(
        "super(messageFromBuilder($L), $L.cause())",
        BuilderSpecs.BUILDER_VAR,
        BuilderSpecs.BUILDER_VAR
      )
      .addStatement("this.altText = builder.altText()")
      .addStatement("this.obj = builder.obj()");
    return method.build();
  }

  /**
   * @return Constructor that that uses {@code RuntimeException}'s getter
   * methods to initialize builder.
   */
  static MethodSpec builderImplConstructor(String packageName) {
    return MethodSpec
      .constructorBuilder()
      .addModifiers(PROTECTED)
      .addParameter(nativeClassName(packageName), "model")
      .addStatement("this.cause = model.getCause()")
      .addStatement("this.message = model.getMessage()")
      .addStatement("this.obj = model.obj()")
      .build();
  }

  static MethodSpec implBuildMethod(ClassName className) {
    return MethodSpec
      .methodBuilder("build")
      .addModifiers(PUBLIC)
      .returns(className)
      .beginControlFlow(
        "if (this.obj != null && this.cause == null && this.obj instanceof Throwable)"
      )
      .addStatement("this.cause = (Throwable) this.obj")
      .nextControlFlow("else if (this.obj == null && this.cause != null)")
      .addStatement("this.obj = this.cause")
      .endControlFlow()
      .addStatement("return new $T(this)", className)
      .build();
  }
}
