// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.library.shims;

import static javax.lang.model.element.Modifier.ABSTRACT;
import static javax.lang.model.element.Modifier.FINAL;
import static javax.lang.model.element.Modifier.PRIVATE;
import static javax.lang.model.element.Modifier.PUBLIC;
import static software.amazon.smithy.utils.StringUtils.uncapitalize;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.FieldSpec;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeSpec;
import com.squareup.javapoet.TypeVariableName;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;
import software.amazon.polymorph.smithyjava.MethodSignature;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.polymorph.smithyjava.generator.library.ShimLibrary;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.smithyjava.nameresolver.Native;
import software.amazon.polymorph.traits.ExtendableTrait;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ResourceShape;

public class ResourceShim extends ShimLibrary {

  private static final String TYPE_VAR = "I";
  /** Factory Method name. */
  public static final String WRAP_METHOD_NAME = "wrap";
  /** The Resource Shape the Shim wraps. */
  protected final ResourceShape targetShape;
  protected final ClassName interfaceName;
  /** The class name of the Subject's Shim class. */
  protected final ClassName thisClassName;
  protected final boolean extendable;
  private final ClassName dafnyType;
  private final String argName;

  public ResourceShim(JavaLibrary javaLibrary, ResourceShape targetShape) {
    super(javaLibrary);
    this.targetShape = targetShape;
    this.thisClassName =
      subject.nativeNameResolver.classNameForResource(targetShape);
    this.interfaceName = interfaceName(targetShape, subject.sdkVersion);
    this.extendable = targetShape.hasTrait(ExtendableTrait.class);
    dafnyType = Dafny.interfaceForResource(this.targetShape);
    argName = uncapitalize(dafnyType.simpleName());
  }

  private static ClassName interfaceName(
    ResourceShape shape,
    CodegenSubject.AwsSdkVersion sdkVersion
  ) {
    return Native.classNameForInterfaceOrLocalService(shape, sdkVersion);
  }

  private TypeVariableName iExtendsInterface() {
    return TypeVariableName.get(TYPE_VAR, interfaceName);
  }

  @Override
  public Set<JavaFile> javaFiles() {
    LinkedHashSet<JavaFile> rtn = new LinkedHashSet<>(2);
    rtn.add(JavaFile.builder(thisClassName.packageName(), shim()).build());
    rtn.add(
      JavaFile
        .builder(thisClassName.packageName(), publicResourceInterface())
        .build()
    );
    return rtn;
  }

  TypeSpec shim() {
    TypeSpec.Builder spec = TypeSpec
      .classBuilder(thisClassName)
      .addModifiers(PUBLIC, FINAL)
      .addField(getField())
      .addSuperinterface(interfaceName)
      .addMethod(constructor())
      .addMethod(resourceAsDafny())
      .addMethod(resourceAsNativeInterface())
      .addMethod(impl());
    ModelUtils.getDocumentationOrJavadoc(targetShape).map(spec::addJavadoc);
    spec.addMethods(
      getOperationsForTarget()
        .stream()
        .map(this::operation)
        .collect(Collectors.toList())
    );
    if (extendable) {
      NativeWrapper wrapper = new NativeWrapper(subject, targetShape);
      spec.addType(wrapper.nativeWrapper());
    }
    return spec.build();
  }

  private CodeBlock nonNull() {
    return CodeBlock.of(
      "$T.requireNonNull($L, $S)",
      Objects.class,
      argName,
      "Missing value for required argument `%s`".formatted(argName)
    );
  }

  private MethodSpec constructor() {
    return MethodSpec
      .constructorBuilder()
      .addModifiers(PRIVATE)
      .addParameter(dafnyType, argName)
      .addStatement(nonNull())
      .addStatement("this.$L = $L", INTERFACE_FIELD, argName)
      .build();
  }

  private MethodSpec resourceAsNativeInterface() {
    MethodSpec.Builder method = MethodSpec
      .methodBuilder(WRAP_METHOD_NAME)
      .addModifiers(PUBLIC_STATIC)
      .addTypeVariable(iExtendsInterface())
      .addParameter(iExtendsInterface(), argName)
      .returns(thisClassName)
      .addStatement(nonNull())
      .beginControlFlow("if ($L instanceof $L)", argName, thisClassName)
      .addStatement("return (($T) $L)", thisClassName, argName)
      .endControlFlow();
    if (extendable) {
      return method
        // return Resource.create(new NativeWrapper(iResource));
        .addStatement(
          "return $T.$L(new $T($L))",
          thisClassName,
          WRAP_METHOD_NAME,
          NativeWrapper.className(thisClassName),
          argName
        )
        .build();
    }
    return method
      .addStatement(
        "throw new $T($S)",
        IllegalArgumentException.class,
        "Custom implementations of %s are NOT supported at this time.".formatted(
            interfaceName
          )
      )
      .build();
  }

  public MethodSpec resourceAsDafny() {
    return MethodSpec
      .methodBuilder(WRAP_METHOD_NAME)
      .addModifiers(PUBLIC_STATIC)
      .addParameter(dafnyType, argName)
      .returns(thisClassName)
      .addStatement("return new $T($L)", thisClassName, argName)
      .build();
  }

  TypeSpec publicResourceInterface() {
    TypeSpec.Builder spec = TypeSpec
      .interfaceBuilder(interfaceName)
      .addModifiers(PUBLIC);
    spec.addMethods(
      getOperationsForTarget()
        .stream()
        .sequential()
        .map(this::operationMethodSignature)
        .map(MethodSignature::method)
        .map(method -> method.addModifiers(PUBLIC, ABSTRACT))
        .map(MethodSpec.Builder::build)
        .collect(Collectors.toList())
    );
    return spec.build();
  }

  protected MethodSpec impl() {
    return implMethodSignature()
      .addModifiers(PUBLIC)
      .addStatement("return this.$L", INTERFACE_FIELD)
      .build();
  }

  protected MethodSpec.Builder implMethodSignature() {
    return MethodSpec
      .methodBuilder("impl")
      .returns(Dafny.interfaceForResource(targetShape));
  }

  private FieldSpec getField() {
    return FieldSpec
      .builder(Dafny.interfaceForResource(targetShape), INTERFACE_FIELD)
      .addModifiers(PRIVATE_FINAL)
      .build();
  }

  protected List<OperationShape> getOperationsForTarget() {
    return targetShape
      .getOperations()
      .stream()
      .sorted()
      .map(shapeId -> subject.model.expectShape(shapeId, OperationShape.class))
      .collect(Collectors.toList());
  }
}
