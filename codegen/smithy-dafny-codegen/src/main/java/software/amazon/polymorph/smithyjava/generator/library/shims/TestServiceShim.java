// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.library.shims;

import static javax.lang.model.element.Modifier.PROTECTED;
import static javax.lang.model.element.Modifier.PUBLIC;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.FieldSpec;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeSpec;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;
import software.amazon.polymorph.smithyjava.BuildMethod;
import software.amazon.polymorph.smithyjava.BuilderMemberSpec;
import software.amazon.polymorph.smithyjava.BuilderSpecs;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.polymorph.smithyjava.modeled.Operation;
import software.amazon.smithy.model.shapes.ServiceShape;

public class TestServiceShim extends ServiceShim {

  /** The Service Shape this Shim Tests. */
  protected final ServiceShape targetShape;
  /** The class name of the Subject's Test Shim class. */
  protected final ClassName thisClassName;

  public TestServiceShim(JavaLibrary javaLibrary, ServiceShape targetShape) {
    super(javaLibrary, targetShape);
    this.targetShape = targetShape;
    this.thisClassName =
      subject.nativeNameResolver.classNameForTestService(targetShape);
  }

  @Override
  public Set<JavaFile> javaFiles() {
    JavaFile.Builder shimFile = JavaFile.builder(
      thisClassName.packageName(),
      shim()
    );
    return Collections.singleton(shimFile.build());
  }

  @Override
  protected TypeSpec shim() {
    TypeSpec.Builder spec = TypeSpec
      .classBuilder(thisClassName)
      .addSuperinterface(
        subject.dafnyNameResolver.classNameForInterface(this.targetShape)
      )
      .addModifiers(PUBLIC)
      .addField(getField());
    BuilderSpecs builderSpecs = new BuilderSpecs(
      thisClassName,
      null,
      List.of(getArg()),
      Collections.emptyList()
    );
    // Add the Builder Interface
    spec.addType(builderSpecs.builderInterface());
    // Add the Builder Implementation
    spec.addType(
      builderSpecs.builderImpl(false, null, testServiceBuilderImplBuildMethod())
    );
    // Add the class's constructor
    spec.addMethod(testServiceConstructor(builderSpecs));
    // Add public static method for creating a builder
    spec.addMethod(builderSpecs.builderMethod());

    spec.addMethods(
      getOperationsForTarget()
        .stream()
        .map(shape -> Operation.AsDafny.operation(shape, this.subject, this))
        .collect(Collectors.toList())
    );
    return spec.build();
  }

  /** The only argument for a shim testing a local service is an instance of the local service.*/
  private BuilderMemberSpec getArg() {
    return BuilderMemberSpec.localServiceAsMemberSpec(this.subject);
  }

  /** The only field for a shim testing a local service is an instance of the local service.*/
  private FieldSpec getField() {
    return FieldSpec
      .builder(
        subject.nativeNameResolver.classNameForService(subject.serviceShape),
        INTERFACE_FIELD
      )
      .addModifiers(PRIVATE_FINAL)
      .build();
  }

  /*
    The test shim takes the library's public client.
    A little like the classes in software.amazon.polymorph.smithyjava.unmodeled,
    there are elements of the library's test shim
    that are not modeled in a traditional smithy way.
    In particular, we REQUIRE an instance of the library's public client,
    but there is no @required annotation (or equivalent)
    to inform Smithy that the test shim needs an instance of the public client.
     */
  private MethodSpec testServiceBuilderImplBuildMethod() {
    return MethodSpec
      .methodBuilder("build")
      .addModifiers(PUBLIC)
      .returns(thisClassName)
      .addCode(BuildMethod.requiredCheck(getArg()))
      .addStatement("return new $T(this)", thisClassName)
      .build();
  }

  private MethodSpec testServiceConstructor(BuilderSpecs builderSpecs) {
    MethodSpec.Builder method = MethodSpec
      .constructorBuilder()
      .addModifiers(PROTECTED)
      .addParameter(builderSpecs.builderImplName(), BuilderSpecs.BUILDER_VAR);
    method.addStatement(
      "this.$L = $L.$L()",
      getField().name,
      BuilderSpecs.BUILDER_VAR,
      getArg().name
    );
    return method.build();
  }
}
