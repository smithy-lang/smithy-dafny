// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.library.shims;

import static javax.lang.model.element.Modifier.PROTECTED;
import static javax.lang.model.element.Modifier.PUBLIC;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.FieldSpec;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeName;
import com.squareup.javapoet.TypeSpec;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import software.amazon.polymorph.smithyjava.BuildMethod;
import software.amazon.polymorph.smithyjava.BuilderMemberSpec;
import software.amazon.polymorph.smithyjava.BuilderSpecs;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.polymorph.smithyjava.generator.library.ShimLibrary;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.shapes.ServiceShape;

public class ServiceShim extends ShimLibrary {

  /** The Service Shape the Shim wraps. */
  protected final ServiceShape targetShape;
  /** The class name of the Subject's Shim class. */
  protected final ClassName thisClassName;

  public ServiceShim(JavaLibrary javaLibrary, ServiceShape targetShape) {
    super(javaLibrary);
    this.targetShape = targetShape;
    this.thisClassName =
      subject.nativeNameResolver.classNameForService(targetShape);
  }

  @Override
  public Set<JavaFile> javaFiles() {
    JavaFile.Builder shimFile = JavaFile.builder(
      thisClassName.packageName(),
      shim()
    );
    return Collections.singleton(shimFile.build());
  }

  protected TypeSpec shim() {
    TypeSpec.Builder spec = TypeSpec
      .classBuilder(thisClassName)
      .addModifiers(PUBLIC)
      .addField(getField());
    List<BuilderMemberSpec> shimArgs = List.of(getArg());
    BuilderSpecs builderSpecs = new BuilderSpecs(
      thisClassName,
      null,
      shimArgs,
      Collections.emptyList()
    );
    ModelUtils.getDocumentationOrJavadoc(targetShape).map(spec::addJavadoc);
    spec
      .addType(builderSpecs.builderInterface())
      .addType(
        builderSpecs.builderImpl(false, null, serviceBuilderImplBuildMethod())
      )
      .addMethod(serviceConstructor(builderSpecs))
      .addMethod(builderSpecs.builderMethod())
      .addMethod(dafnyConstructor());

    spec.addMethods(
      getOperationsForTarget()
        .stream()
        .map(this::operation)
        .collect(Collectors.toList())
    );
    spec.addMethod(impl());
    return spec.build();
  }

  private BuilderMemberSpec getArg() {
    LocalServiceTrait trait = targetShape.expectTrait(LocalServiceTrait.class);
    return BuilderMemberSpec.localServiceConfigMemberSpec(trait, subject);
  }

  private FieldSpec getField() {
    return FieldSpec
      .builder(
        subject.dafnyNameResolver.typeForShape(targetShape.toShapeId()),
        INTERFACE_FIELD
      )
      .addModifiers(PRIVATE_FINAL)
      .build();
  }

  /*
    The shim is the library's public client.
    A little like the classes in software.amazon.polymorph.smithyjava.unmodeled,
    there are elements of the library's public client
    that are not modeled in a traditional smithy way.
    In particular, we REQUIRE a Config object,
    but there is no @required annotation (or equivalent)
    to inform Smithy that the service client needs a config.
     */
  private MethodSpec serviceBuilderImplBuildMethod() {
    return MethodSpec
      .methodBuilder("build")
      .addModifiers(PUBLIC)
      .returns(thisClassName)
      .addCode(BuildMethod.requiredCheck(getArg()))
      .addStatement("return new $T(this)", thisClassName)
      .build();
  }

  private MethodSpec serviceConstructor(BuilderSpecs builderSpecs) {
    LocalServiceTrait trait = targetShape.expectTrait(LocalServiceTrait.class);
    MethodSpec.Builder method = MethodSpec
      .constructorBuilder()
      .addModifiers(PROTECTED)
      .addParameter(builderSpecs.builderImplName(), BuilderSpecs.BUILDER_VAR);
    // get config from builder
    // i.e: CryptoConfig nativeConfig = builder.CryptoConfig();
    method.addStatement(
      "$T $L = $L.$L()",
      getArg().type,
      NATIVE_VAR,
      BuilderSpecs.BUILDER_VAR,
      getArg().name
    );
    // convert config to Dafny
    // i.e: software.amazon.cryptography.primitives.internaldafny.types.CryptoConfig dafnyConfig = ToDafny.CryptoConfig(nativeConfig);
    method.addStatement(dafnyDeclareAndConvert(trait.getConfigId()));
    // Invoke client creation
    // i.e.: Result<AtomicPrimitivesClient, Error> result = software.amazon.cryptography.primitives.internaldafny.__default.AtomicPrimitives(dafnyValue);
    TypeName success =
      subject.dafnyNameResolver.classNameForConcreteServiceClient(
        subject.serviceShape
      );
    TypeName failure = subject.dafnyNameResolver.abstractClassForError();
    TypeName result = Dafny.asDafnyResult(success, failure);
    method.addStatement(
      "$T $L = $T.$L($L)",
      result,
      RESULT_VAR,
      subject.dafnyNameResolver.classNameForNamespaceDefault(),
      thisClassName.simpleName(),
      DAFNY_VAR
    );
    method.addCode(ifFailure());
    method.addStatement(
      "this.$L = $L.dtor_value()",
      INTERFACE_FIELD,
      RESULT_VAR
    );
    return method.build();
  }

  protected MethodSpec impl() {
    return MethodSpec
      .methodBuilder(INTERFACE_VAR)
      .addModifiers(PROTECTED)
      .addStatement("return this.$L", INTERFACE_FIELD)
      .returns(Dafny.interfaceForService(this.targetShape))
      .build();
  }

  private MethodSpec dafnyConstructor() {
    FieldSpec dafnyInterfaceField = getField();
    return MethodSpec
      .constructorBuilder()
      .addParameter(dafnyInterfaceField.type, INTERFACE_VAR)
      .addStatement("this.$L = $L", INTERFACE_FIELD, INTERFACE_VAR)
      .build();
  }
}
