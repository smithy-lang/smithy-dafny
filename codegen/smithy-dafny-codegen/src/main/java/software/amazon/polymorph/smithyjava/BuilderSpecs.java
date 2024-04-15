// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava;

import static javax.lang.model.element.Modifier.ABSTRACT;
import static javax.lang.model.element.Modifier.PRIVATE;
import static javax.lang.model.element.Modifier.PROTECTED;
import static javax.lang.model.element.Modifier.PUBLIC;
import static javax.lang.model.element.Modifier.STATIC;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.FieldSpec;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeName;
import com.squareup.javapoet.TypeSpec;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import javax.lang.model.element.Modifier;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.smithy.model.shapes.Shape;

/** Creates a Builder Interface and Implementation for a Shape. */
public class BuilderSpecs {

  /** Also the name of the method to initialize a builder. */
  public static String BUILDER_VAR = "builder";

  @Nonnull
  private final ClassName className;

  @Nullable
  private final ClassName superName;

  @Nonnull
  private final List<BuilderMemberSpec> localFields;

  @Nonnull
  private final List<BuilderMemberSpec> superFields;

  public static List<BuilderMemberSpec> shapeToArgs(
    Shape shape,
    JavaLibrary subject
  ) {
    return shape
      .members()
      .stream()
      .map(member -> new BuilderMemberSpec(member, subject))
      .collect(Collectors.toList());
  }

  // TODO: We have removed all users of superName & superFields,
  //  and have no tests for their usage.
  //  We SHOULD remove them entirely.
  public BuilderSpecs(
    @Nonnull ClassName className,
    @Nullable ClassName superName,
    @Nonnull List<BuilderMemberSpec> localFields,
    @Nonnull List<BuilderMemberSpec> superFields
  ) {
    if (superName == null && superFields.size() != 0) {
      throw new IllegalArgumentException(
        "Cannot provide a populated superFields but no superName"
      );
    }
    this.className = className;
    this.superName = superName;
    this.superFields = superFields;
    Set<String> superFieldNames =
      this.superFields.stream()
        .map(field -> field.name)
        .collect(Collectors.toSet());
    this.localFields =
      localFields
        .stream()
        .filter(field -> !superFieldNames.contains(field.name))
        .collect(Collectors.toList());
  }

  public static ClassName builderInterfaceName(ClassName className) {
    return className.nestedClass("Builder");
  }

  static ClassName builderImplName(ClassName className) {
    return className.nestedClass("BuilderImpl");
  }

  public ClassName builderInterfaceName() {
    return builderInterfaceName(className);
  }

  public ClassName builderImplName() {
    return builderImplName(className);
  }

  /**
   * The Builder Interface defines the builder's
   * getter, setters, and build method.<p>
   * Note: The method that takes an instance of the class and
   * returns a builder derived from that an instance,
   * (here, called the modelConstructor)
   * is NOT defined in the interface.
   * @return The nested public interface "Builder".
   */
  public TypeSpec builderInterface() {
    TypeSpec.Builder builder = TypeSpec
      .interfaceBuilder(builderInterfaceName())
      .addModifiers(PUBLIC);
    if (superName != null) {
      builder.addSuperinterface(builderInterfaceName(superName));
    }
    superFields.forEach(field -> builder.addMethod(interfaceSetter(field)));
    localFields.forEach(field -> {
      builder.addMethod(interfaceSetter(field));
      builder.addMethod(interfaceGetter(field));
    });
    builder.addMethod(builderInterfaceBuildMethod());
    return builder.build();
  }

  @Nonnull
  private MethodSpec interfaceGetter(BuilderMemberSpec field) {
    MethodSpec.Builder method = MethodSpec
      .methodBuilder(field.name)
      .returns(field.type)
      .addModifiers(PUBLIC, ABSTRACT);
    if (Objects.nonNull(field.javaDoc)) {
      method.addJavadoc("@return $L", field.javaDoc);
    }
    return method.build();
  }

  @Nonnull
  private MethodSpec interfaceSetter(BuilderMemberSpec field) {
    MethodSpec.Builder method = MethodSpec
      .methodBuilder(field.name)
      // If the type is a Reference to a Resource, the method should take an interface
      .addParameter(
        field.interfaceType != null ? field.interfaceType : field.type,
        field.name
      )
      .returns(builderInterfaceName())
      .addModifiers(ABSTRACT, PUBLIC);
    if (Objects.nonNull(field.javaDoc)) {
      method.addJavadoc("@param $L $L", field.name, field.javaDoc);
    }
    return method.build();
  }

  private MethodSpec builderInterfaceBuildMethod() {
    return MethodSpec
      .methodBuilder("build")
      .returns(className)
      .addModifiers(PUBLIC, ABSTRACT)
      .build();
  }

  /**
   * @param overrideSuper If True, add Override annotation to `build` and to "builder setter" methods from superFields
   * @param modelConstructor The Constructor for the BuilderImpl that takes an instance of the class and
   *                         uses the instance's fields to initialize the builder.<p>
   *                         If null, no modelConstructor is generated.
   * @param buildMethod  The `build` method of a Builder(Impl) returns a new instance of the class.
   *                     For modeled shapes, use {@link BuildMethod#implBuildMethod}
   *                     to generate a method that respects smithy constraint traits.
   * @return The nested public class that implements the Builder Interface.
   */
  public TypeSpec builderImpl(
    // TODO: We have removed all use of overrideSuper,
    //  and have no tests for it usage.
    //  We SHOULD remove it entirely.
    boolean overrideSuper,
    @Nullable MethodSpec modelConstructor,
    @Nonnull MethodSpec buildMethod
  ) {
    if (overrideSuper && superName == null) {
      throw new IllegalArgumentException(
        "Cannot overrideSuper if there is no super"
      );
    }
    TypeSpec.Builder builder = TypeSpec
      .classBuilder(builderImplName())
      .addSuperinterface(builderInterfaceName())
      .addModifiers(STATIC);
    if (superName != null) {
      builder.superclass(builderImplName(superName));
    }
    // Add Fields
    localFields.forEach(field -> addField(builder, field));
    // Add Constructors
    builder.addMethod(
      MethodSpec.constructorBuilder().addModifiers(PROTECTED).build()
    );
    if (Objects.nonNull(modelConstructor)) {
      builder.addMethod(modelConstructor);
    }
    // for local fields
    localFields.forEach(field -> {
      // Builder Setter Method
      builder.addMethod(setterMethod(field));
      // Getter Method
      builder.addMethod(
        MethodSpec
          .methodBuilder(field.name)
          .addModifiers(Modifier.PUBLIC)
          .returns(field.type)
          .addStatement("return this.$L", field.name)
          .build()
      );
    });
    // Builder for super's fields
    superFields.forEach(field -> {
      MethodSpec.Builder method = MethodSpec
        .methodBuilder(field.name)
        .returns(builderInterfaceName())
        .addModifiers(Modifier.PUBLIC)
        .addParameter(field.type, field.name)
        .addStatement("super.$L($L)", field.name, field.name)
        .addStatement("return this");
      if (overrideSuper) {
        method.addAnnotation(Override.class);
      }
      builder.addMethod(method.build());
    });
    // build
    builder.addMethod(buildMethod);
    return builder.build();
  }

  private TypeSpec.Builder addField(
    TypeSpec.Builder builder,
    BuilderMemberSpec field
  ) {
    builder.addField(field.type, field.name, PROTECTED);
    // If primitive type, there MUST be a private field to track setting the field
    if (field.type.isPrimitive()) {
      builder.addField(
        FieldSpec
          .builder(TypeName.BOOLEAN, BuildMethod.isSetFieldName(field))
          .addModifiers(PRIVATE)
          .initializer(CodeBlock.of("false"))
          .build()
      );
    }
    return builder;
  }

  private MethodSpec setterMethod(BuilderMemberSpec field) {
    MethodSpec.Builder setter = MethodSpec
      .methodBuilder(field.name)
      .addModifiers(PUBLIC)
      .returns(builderInterfaceName())
      // If the type is a Reference to a Resource, the method should take an interface
      .addParameter(
        field.interfaceType != null ? field.interfaceType : field.type,
        field.name
      )
      // If the type is a Reference to a Resource, and not in AWS-SDK, we need to "wrap" it
      .addStatement(
        "this.$L = $L",
        field.name,
        field.wrapCall != null ? field.wrapCall : field.name
      );
    if (field.type.isPrimitive()) {
      // If primitive type, Setter MUST record that the field was set.
      setter.addStatement("this.$L = true", BuildMethod.isSetFieldName(field));
    }
    return setter.addStatement("return this").build();
  }

  /**
   * @param override If True, add Override annotation
   * @return Method that converts the class to an instance of it's Builder
   */
  // TODO: We have removed all use of override=true,
  //  and have no tests for it usage.
  //  We SHOULD remove it entirely.
  public MethodSpec toBuilderMethod(boolean override) {
    MethodSpec.Builder method = MethodSpec
      .methodBuilder("toBuilder")
      .addModifiers(PUBLIC)
      .returns(builderInterfaceName())
      .addStatement("return new $T(this)", builderImplName());
    if (override) {
      method.addAnnotation(Override.class);
    }
    return method.build();
  }

  /**
   *  Provides the `builder` method for a class;
   *  The `builder` method returns a new Builder(Impl) for the class.
   */
  public MethodSpec builderMethod() {
    MethodSpec.Builder method = MethodSpec
      .methodBuilder("builder")
      .addModifiers(PUBLIC, STATIC)
      .returns(builderInterfaceName())
      .addStatement("return new $T()", builderImplName());
    return method.build();
  }

  /**
   * Provides the default Builder Impl model constructor.
   * That is, the Constructor for the BuilderImpl that takes an instance of
   * the class and uses the instance's fields to initialize the builder.
   * <p>
   * The only reason to not use this is if the super class should not be called,
   * but there is a super (i.e.: NativeError).
   */
  public MethodSpec implModelConstructor() {
    MethodSpec.Builder modelConstructor = MethodSpec
      .constructorBuilder()
      .addModifiers(PROTECTED)
      .addParameter(className, "model");
    if (superName != null) {
      modelConstructor.addStatement("super(model)");
    }
    localFields.forEach(field -> {
      modelConstructor.addStatement(
        "this.$L = model.$L()",
        field.name,
        field.name
      );
      if (field.type.isPrimitive()) {
        // If primitive type, MUST record that the field was set
        modelConstructor.addStatement(
          "this.$L = true",
          BuildMethod.isSetFieldName(field)
        );
      }
    });
    return modelConstructor.build();
  }

  /**
   * Provides a BuilderImpl build method for un-modeled objects
   * (i.e.: staticErrors).
   * The `build` method of a Builder(Impl) returns a new instance of the class.
   * <p>For modeled shapes, use {@link BuildMethod#implBuildMethod}
   * to generate a method that respects smithy constraint traits.
   */
  public MethodSpec implBuildMethod(boolean overrideSuper) {
    MethodSpec.Builder buildMethod = MethodSpec
      .methodBuilder("build")
      .addModifiers(Modifier.PUBLIC)
      .returns(className)
      .addStatement("return new $T(this)", className);
    if (overrideSuper) {
      buildMethod.addAnnotation(Override.class);
    }
    return buildMethod.build();
  }
}
