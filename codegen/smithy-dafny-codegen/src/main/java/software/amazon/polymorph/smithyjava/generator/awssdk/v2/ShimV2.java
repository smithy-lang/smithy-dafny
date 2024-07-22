// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.awssdk.v2;

import static software.amazon.polymorph.smithyjava.nameresolver.Constants.DAFNY_TUPLE0_CLASS_NAME;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.SMITHY_API_UNIT;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeName;
import com.squareup.javapoet.TypeSpec;
import java.util.Collections;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import javax.lang.model.element.Modifier;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import software.amazon.polymorph.smithyjava.generator.Generator;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.utils.DafnyNameResolverHelpers;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.utils.StringUtils;

//TODO: Create abstract class for V1 & V2 to extend
/**
 * Generates an AWS SDK Shim for the AWS SDK for Java V2
 * exposing an AWS Service's operations to Dafny Generated Java.
 */
public class ShimV2 extends Generator {

  public static final String SHIM = "Shim";
  // Hack to override CodegenSubject
  // See code comment on ../library/ModelCodegen for details.
  private final JavaAwsSdkV2 subject;
  private static final Logger LOGGER = LoggerFactory.getLogger(ShimV2.class);

  public ShimV2(JavaAwsSdkV2 awsSdk) {
    super(awsSdk);
    this.subject = awsSdk;
  }

  public static ClassName className(ServiceShape shape) {
    return ClassName.get(
      DafnyNameResolverHelpers.packageNameForNamespace(
        shape.toShapeId().getNamespace()
      ),
      SHIM
    );
  }

  @Override
  public Set<JavaFile> javaFiles() {
    JavaFile.Builder builder = JavaFile.builder(
      subject.dafnyNameResolver.packageName(),
      shim()
    );
    return Collections.singleton(builder.build());
  }

  TypeSpec shim() {
    return TypeSpec
      .classBuilder(
        ClassName.get(subject.dafnyNameResolver.packageName(), "Shim")
      )
      .addModifiers(Modifier.PUBLIC)
      .addSuperinterface(
        subject.dafnyNameResolver.typeForShape(subject.serviceShape.getId())
      )
      .addField(
        subject.nativeNameResolver.classNameForService(subject.serviceShape),
        "_impl",
        Modifier.PRIVATE,
        Modifier.FINAL
      )
      .addField(
        ClassName.get(String.class),
        "region",
        Modifier.PRIVATE,
        Modifier.FINAL
      )
      .addMethod(constructor())
      .addMethod(impl())
      .addMethod(region())
      .addMethods(
        subject.serviceShape
          .getAllOperations()
          .stream()
          .sorted()
          .map(this::operation)
          .filter(Optional::isPresent)
          .map(Optional::get)
          .collect(Collectors.toList())
      )
      .build();
  }

  protected MethodSpec impl() {
    return MethodSpec
      .methodBuilder("impl")
      .addModifiers(Modifier.PUBLIC)
      .addStatement("return this._impl")
      .returns(
        subject.nativeNameResolver.classNameForService(subject.serviceShape)
      )
      .build();
  }

  MethodSpec constructor() {
    return MethodSpec
      .constructorBuilder()
      .addModifiers(Modifier.PUBLIC)
      .addParameter(
        subject.nativeNameResolver.classNameForService(subject.serviceShape),
        "impl",
        Modifier.FINAL
      )
      .addParameter(ClassName.get(String.class), "region", Modifier.FINAL)
      .addStatement("this._impl = impl")
      .addStatement("this.region = region")
      .build();
  }

  MethodSpec region() {
    return MethodSpec
      .methodBuilder("region")
      .addModifiers(Modifier.PUBLIC)
      .returns(ClassName.get(String.class))
      .addStatement("return this.region")
      .build();
  }

  Optional<MethodSpec> operation(final ShapeId operationShapeId) {
    final OperationShape operationShape = subject.model.expectShape(
      operationShapeId,
      OperationShape.class
    );
    ShapeId inputShapeId = operationShape.getInputShape();
    ShapeId outputShapeId = operationShape.getOutputShape();
    TypeName dafnyOutput = subject.dafnyNameResolver.typeForShape(
      outputShapeId
    );
    String operationName = operationShape.toShapeId().getName();
    MethodSpec.Builder builder = MethodSpec
      .methodBuilder(StringUtils.capitalize(operationName))
      .addAnnotation(Override.class)
      .addModifiers(Modifier.PUBLIC)
      .returns(
        Dafny.asDafnyResult(
          dafnyOutput,
          subject.dafnyNameResolver.abstractClassForError()
        )
      )
      .addParameter(
        subject.dafnyNameResolver.typeForShape(inputShapeId),
        "input"
      )
      .addStatement(
        "$T converted = ToNative.$L(input)",
        subject.nativeNameResolver.typeForShape(inputShapeId),
        StringUtils.capitalize(inputShapeId.getName())
      )
      .beginControlFlow("try");
    CodeBlock successTypeDescriptor;
    if (outputShapeId.equals(SMITHY_API_UNIT)) {
      successTypeDescriptor =
        CodeBlock.of(DAFNY_TUPLE0_CLASS_NAME + "._typeDescriptor()");
      builder
        .addStatement(
          "_impl.$L(converted)",
          StringUtils.uncapitalize(operationName)
        )
        .addStatement(
          "return $L",
          subject.dafnyNameResolver.createSuccess(
            successTypeDescriptor,
            CodeBlock.of("$T.create()", DAFNY_TUPLE0_CLASS_NAME)
          )
        );
    } else {
      successTypeDescriptor =
        subject.dafnyNameResolver.typeDescriptor(outputShapeId);
      builder
        .addStatement(
          "$T result = _impl.$L(converted)",
          subject.nativeNameResolver.typeForOperationOutput(outputShapeId),
          StringUtils.uncapitalize(operationName)
        )
        .addStatement(
          "$T dafnyResponse = ToDafny.$L(result)",
          dafnyOutput,
          StringUtils.capitalize(outputShapeId.getName())
        )
        .addStatement(
          "return $L",
          subject.dafnyNameResolver.createSuccess(
            successTypeDescriptor,
            CodeBlock.of("dafnyResponse")
          )
        );
    }

    operationShape
      .getErrors()
      .stream()
      .sorted()
      .forEach(shapeId -> {
        TypeName typeForShape = subject.nativeNameResolver.typeForShape(
          shapeId
        );

        // InvalidEndpointException was removed in SDK V2
        if (typeForShape.toString().endsWith("InvalidEndpointException")) {
          return; // Skips only this shape
        }

        builder
          .nextControlFlow(
            "catch ($T ex)",
            subject.nativeNameResolver.typeForShape(shapeId)
          )
          .addStatement(
            "return $L",
            subject.dafnyNameResolver.createFailure(
              successTypeDescriptor,
              CodeBlock.of("ToDafny.Error(ex)")
            )
          );
      });
    builder
      .nextControlFlow(
        "catch ($T ex)",
        subject.nativeNameResolver.baseErrorForService()
      )
      .addStatement(
        "return $L",
        subject.dafnyNameResolver.createFailure(
          successTypeDescriptor,
          CodeBlock.of("ToDafny.Error(ex)")
        )
      );
    builder
      .nextControlFlow("catch (Exception ex)")
      .addStatement(
        "return $L",
        subject.dafnyNameResolver.createFailure(
          successTypeDescriptor,
          CodeBlock.of("ToDafny.Error(ex)")
        )
      );
    return Optional.of(builder.endControlFlow().build());
  }
}
