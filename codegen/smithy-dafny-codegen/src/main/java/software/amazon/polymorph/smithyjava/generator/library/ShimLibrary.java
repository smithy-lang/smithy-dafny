// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.library;

import static javax.lang.model.element.Modifier.PUBLIC;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.DAFNY_TUPLE0_CLASS_NAME;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.SMITHY_API_UNIT;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeName;
import java.util.Optional;
import software.amazon.awssdk.utils.StringUtils;
import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.polymorph.smithyjava.MethodSignature;
import software.amazon.polymorph.smithyjava.OperationJavaDoc;
import software.amazon.polymorph.smithyjava.generator.Generator;
import software.amazon.polymorph.smithyjava.modeled.Operation;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.ModelUtils.ResolvedShapeId;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;

/**
 * A Java Library's Shim is the public class
 * that consumers interact with in Native Java.<p>
 * ShimLibrary holds the logic required to generate the Shim.
 */
public abstract class ShimLibrary extends Generator {

  // Hack to override CodegenSubject
  // See ModelCodegen for explanation
  protected final JavaLibrary subject;
  /** The class name of the Subject's ToDafny class. */
  public final ClassName toDafnyClassName;
  /** The class name of the Subject's ToNative class. */
  public final ClassName toNativeClassName;

  public ShimLibrary(JavaLibrary javaLibrary) {
    super(javaLibrary);
    this.subject = javaLibrary;
    this.toDafnyClassName = ToDafnyLibrary.className(javaLibrary);
    this.toNativeClassName = ToNativeLibrary.className(javaLibrary);
  }

  // TODO: The methods in this class SHOULD all be moved to
  //  software.amazon.polymorph.smithyjava.modeled.Operation.AsNative,
  //  which, ideally, would become a Shape Visitor?
  protected MethodSignature operationMethodSignature(OperationShape shape) {
    final ResolvedShapeId inputResolved = ModelUtils.resolveShape(
      shape.getInputShape(),
      subject.model
    );
    final ResolvedShapeId outputResolved = ModelUtils.resolveShape(
      shape.getOutputShape(),
      subject.model
    );
    final String operationName = shape.toShapeId().getName();
    final MethodSpec.Builder method = MethodSpec
      .methodBuilder(operationName)
      .addModifiers(PUBLIC);
    // if operation takes an argument
    if (!inputResolved.resolvedId().equals(SMITHY_API_UNIT)) {
      TypeName inputType = methodSignatureTypeName(inputResolved);
      method.addParameter(inputType, NATIVE_VAR);
    }
    // if operation is not void
    if (!outputResolved.resolvedId().equals(SMITHY_API_UNIT)) {
      TypeName outputType = methodSignatureTypeName(outputResolved);
      method.returns(outputType);
    }
    String maybeJavaDoc = OperationJavaDoc
      .fromOperationShape(subject.model, shape)
      .getDoc();
    if (StringUtils.isNotBlank(maybeJavaDoc)) {
      method.addJavadoc(maybeJavaDoc);
    }
    return new MethodSignature(method, inputResolved, outputResolved);
  }

  /** @return TypeName for a method's signature. */
  protected TypeName methodSignatureTypeName(ResolvedShapeId resolvedShape) {
    return Operation.preferNativeInterface(resolvedShape, subject);
  }

  protected MethodSpec operation(OperationShape operationShape) {
    final MethodSignature signature = operationMethodSignature(operationShape);
    final ResolvedShapeId inputResolved = signature.resolvedInput();
    final ResolvedShapeId outputResolved = signature.resolvedOutput();
    MethodSpec.Builder method = signature.method();
    final String operationName = operationShape.toShapeId().getName();
    // if operation takes an argument
    if (!inputResolved.resolvedId().equals(SMITHY_API_UNIT)) {
      Shape shape = subject.model.expectShape(inputResolved.resolvedId());
      // If input is a Service or Resource, and Not in AWS Namespace
      if (
        (shape.isServiceShape() || shape.isResourceShape()) &&
        !AwsSdkNameResolverHelpers.isInAwsSdkNamespace(
          inputResolved.resolvedId()
        )
      ) {
        // if operation takes a non-AWS Service/Resource, get impl()
        method.addStatement(dafnyDeclareGetImpl(inputResolved.resolvedId()));
      } else {
        // Convert from nativeValue to dafnyValue
        method.addStatement(dafnyDeclareAndConvert(inputResolved));
      }
    }
    // A void result in Dafny Java is Tuple0
    TypeName success = DAFNY_TUPLE0_CLASS_NAME;
    // if operation is not void
    if (!outputResolved.resolvedId().equals(SMITHY_API_UNIT)) {
      // Replace Tuple0 with real type
      success =
        subject.dafnyNameResolver.typeForShape(outputResolved.resolvedId());
    }
    TypeName failure = subject.dafnyNameResolver.abstractClassForError();
    //TODO: handle operation specific errors?
    TypeName result = Dafny.asDafnyResult(success, failure);
    // if operation takes an argument
    if (!inputResolved.resolvedId().equals(SMITHY_API_UNIT)) {
      // call with that argument in dafny
      method.addStatement(
        "$T $L = this.$L.$L($L)",
        result,
        RESULT_VAR,
        INTERFACE_FIELD,
        operationName,
        DAFNY_VAR
      );
    } else {
      // call with no args
      method.addStatement(
        "$T $L = this.$L.$L()",
        result,
        RESULT_VAR,
        INTERFACE_FIELD,
        operationName
      );
    }
    // Handle Failure
    method.addCode(ifFailure());

    // if operation is void
    if (outputResolved.resolvedId().equals(SMITHY_API_UNIT)) {
      return method.build();
    }
    Shape outputShape = subject.model.expectShape(outputResolved.resolvedId());
    // if resolvedOutput is a Service or Resource not in AWS SDK Namespace
    if (
      (outputShape.isServiceShape() || outputShape.isResourceShape()) &&
      !AwsSdkNameResolverHelpers.isInAwsSdkNamespace(
        outputResolved.resolvedId()
      )
    ) {
      // if operation outputs a non-AWS Service/Resource, wrap result with Shim
      method.addStatement(
        "return $L",
        subject.wrapWithShim(
          outputResolved.resolvedId(),
          CodeBlock.of("$L.dtor_value()", RESULT_VAR)
        )
      );
      return method.build();
    }
    final Shape naiveShape = subject.model.expectShape(
      outputResolved.naiveId()
    );
    final MethodReference toNativeMethod =
      subject.toNativeLibrary.conversionMethodReference(naiveShape);
    // else convert success to native and return
    method.addStatement(
      "return $L($L.dtor_value())",
      toNativeMethod.asNormalReference(),
      RESULT_VAR
    );
    return method.build();
  }

  // If it is known the Shape cannot have a positional trait,
  // then the "targetId" and the "shapeId" are the same.
  protected CodeBlock dafnyDeclareAndConvert(ShapeId shapeId) {
    return dafnyDeclareAndConvert(new ResolvedShapeId(shapeId, shapeId));
  }

  // Positional complicates everything.
  // The types need to be looked up by targetId.
  // But The converters are named after the shapeId.
  protected CodeBlock dafnyDeclareAndConvert(ResolvedShapeId resolvedShape) {
    final ShapeId targetId = resolvedShape.resolvedId();
    final Shape naiveShape = subject.model.expectShape(resolvedShape.naiveId());
    final MethodReference toDafnyMethod =
      subject.toDafnyLibrary.conversionMethodReference(naiveShape);
    return CodeBlock.of(
      "$T $L = $L($L)",
      subject.dafnyNameResolver.typeForShape(targetId),
      DAFNY_VAR,
      toDafnyMethod.asNormalReference(),
      NATIVE_VAR
    );
  }

  protected CodeBlock dafnyDeclare(ShapeId targetId) {
    return CodeBlock.of(
      "$T $L = $L",
      subject.dafnyNameResolver.typeForShape(targetId),
      DAFNY_VAR,
      NATIVE_VAR
    );
  }

  protected CodeBlock dafnyDeclareGetImpl(ShapeId targetId) {
    return CodeBlock.of("$L.impl()", dafnyDeclare(targetId));
  }

  protected CodeBlock ifFailure() {
    return CodeBlock
      .builder()
      .beginControlFlow("if ($L.is_Failure())", RESULT_VAR)
      .addStatement(
        "throw $T.Error($L.dtor_error())",
        toNativeClassName,
        RESULT_VAR
      )
      .endControlFlow()
      .build();
  }
}
