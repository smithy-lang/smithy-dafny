// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.modeled;

import static javax.lang.model.element.Modifier.PUBLIC;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.DAFNY_RESULT_CLASS_NAME;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.DAFNY_TUPLE0_CLASS_NAME;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.SMITHY_API_UNIT;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeName;
import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.polymorph.smithyjava.MethodSignature;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.polymorph.smithyjava.generator.Generator;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.polymorph.smithyjava.generator.library.ShimLibrary;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.smithyjava.nameresolver.Native;
import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.ModelUtils.ResolvedShapeId;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.Shape;

/** Logic for generating Operations.*/
public class Operation {

  public static final String DAFNY_INPUT = "dafnyInput";
  public static final String NATIVE_INPUT = "nativeInput";
  public static final String NATIVE_OUTPUT = "nativeOutput";
  public static final String DAFNY_OUTPUT = "dafnyOutput";

  /** Logic for Generating a Method from an Operation Shape
   * who's input and output are Dafny-Java. */
  public static class AsDafny {

    /** Generate a Method from an operation shape. */
    // TODO: Rather than accept a CodegenSubject & ShimLibrary,
    //  there SHOULD exist some common Record/Class b/w
    //  JavaLibrary & JavaAwsSdk that facilitates To(Native,Dafny) class lookup
    // TODO: AWS-SDK generators should use this method
    public static MethodSpec operation(
      final OperationShape operationShape,
      JavaLibrary subject,
      ShimLibrary shimLibrary
    ) {
      final MethodSignature signature = methodSignature(
        operationShape,
        false,
        subject
      );
      final ResolvedShapeId inputResolved = signature.resolvedInput();
      final ResolvedShapeId outputResolved = signature.resolvedOutput();
      MethodSpec.Builder method = signature.method();
      final String operationName = operationShape.toShapeId().getName();
      // Try native implementation
      method.beginControlFlow("try");
      // Convert Input
      method.addStatement(declareNativeInputAndCovert(inputResolved, subject));
      CodeBlock successTypeDescriptor;
      if (outputResolved.resolvedId().equals(SMITHY_API_UNIT)) {
        // if operation is void
        successTypeDescriptor = CodeBlock.of("dafny.Tuple0._typeDescriptor()");
        method
          .addStatement(invoke(operationName))
          .addStatement(
            "return $L",
            subject.dafnyNameResolver.createSuccess(
              successTypeDescriptor,
              CodeBlock.of("$T.create()", DAFNY_TUPLE0_CLASS_NAME)
            )
          );
      } else {
        // operation is not void
        successTypeDescriptor =
          subject.dafnyNameResolver.typeDescriptor(outputResolved.resolvedId());
        TypeName nativeOutputType = preferNativeInterface(
          outputResolved,
          subject
        );
        method
          .addStatement(
            declareNativeOutputAndInvoke(operationName, nativeOutputType)
          )
          .addStatement(declareDafnyOutputAndConvert(outputResolved, subject))
          .addStatement(
            "return $L",
            subject.dafnyNameResolver.createSuccess(
              successTypeDescriptor,
              CodeBlock.of(DAFNY_OUTPUT)
            )
          );
      }
      // catch Errors in this Namespace
      method
        .nextControlFlow("catch ($T ex)", ClassName.get(RuntimeException.class))
        .addStatement(
          "return $L",
          subject.dafnyNameResolver.createFailure(
            successTypeDescriptor,
            CodeBlock.of("$T.Error(ex)", shimLibrary.toDafnyClassName)
          )
        )
        .endControlFlow();
      return method.build();
    }

    public static MethodSignature methodSignature(
      final OperationShape shape,
      boolean append_k,
      CodegenSubject subject
    ) {
      final ResolvedShapeId inputResolved = ModelUtils.resolveShape(
        shape.getInputShape(),
        subject.model
      );
      final ResolvedShapeId outputResolved = ModelUtils.resolveShape(
        shape.getOutputShape(),
        subject.model
      );
      final String operationName = append_k
        ? shape.toShapeId().getName() + "_k" // See JavaDoc on operation_K below
        : shape.toShapeId().getName();
      final MethodSpec.Builder method = MethodSpec
        .methodBuilder(operationName)
        .addModifiers(PUBLIC);
      // if operation takes an argument
      if (!inputResolved.resolvedId().equals(SMITHY_API_UNIT)) {
        TypeName inputType = methodInputSignatureTypeName(
          inputResolved,
          subject
        );
        method.addParameter(inputType, DAFNY_INPUT);
      }
      TypeName outputType = methodOutputTypeName(outputResolved, subject);
      method.returns(outputType);
      return new MethodSignature(method, inputResolved, outputResolved);
    }

    /** @return TypeName for a method's signature.*/
    static TypeName methodInputSignatureTypeName(
      final ResolvedShapeId resolvedShape,
      CodegenSubject subject
    ) {
      return preferDafnyInterface(resolvedShape, subject);
    }

    /** @return TypeName for a method's signature.*/
    static TypeName methodOutputTypeName(
      final ResolvedShapeId resolvedShape,
      CodegenSubject subject
    ) {
      final TypeName success = preferDafnyInterface(resolvedShape, subject);
      TypeName failure = subject.dafnyNameResolver.abstractClassForError();
      return Dafny.asDafnyResult(success, failure);
    }

    /** Declare the Idiomatic-Java input and
     * assign the conversion of the Dafny-Java object to it. */
    // TODO: this method may not handle AWS-SDK shapes correctly!
    static CodeBlock declareNativeInputAndCovert(
      final ResolvedShapeId resolvedShape,
      JavaLibrary subject
    ) {
      CodeBlock leftHand = CodeBlock.of(
        "$T $L",
        subject.nativeNameResolver.typeForShape(resolvedShape.resolvedId()),
        NATIVE_INPUT
      );
      final Shape naiveShape = subject.model.expectShape(
        resolvedShape.naiveId()
      );
      final MethodReference toNativeMethod =
        subject.toNativeLibrary.conversionMethodReference(naiveShape);
      return CodeBlock.of(
        "$L = $L($L)",
        leftHand,
        toNativeMethod.asNormalReference(),
        DAFNY_INPUT
      );
    }

    /** Declare the Idiomatic-Java output and
     * assign the result of the operation invocation to it. */
    static CodeBlock declareNativeOutputAndInvoke(
      final String operationName,
      final TypeName nativeOutputType
    ) {
      return CodeBlock.of(
        "$T $L = $L",
        nativeOutputType,
        NATIVE_OUTPUT,
        invoke(operationName)
      );
    }

    /** Invoke the operation. */
    static CodeBlock invoke(final String operationName) {
      return CodeBlock.of(
        "this.$L.$L($L)",
        Generator.INTERFACE_FIELD,
        operationName,
        NATIVE_INPUT
      );
    }

    /** Declare the Dafny-Java output and
     * assign the result of converting the Idiomatic-Java output to it. */
    static CodeBlock declareDafnyOutputAndConvert(
      final ResolvedShapeId resolvedShape,
      JavaLibrary subject
    ) {
      CodeBlock leftHand = CodeBlock.of(
        "$T $L",
        subject.dafnyNameResolver.typeForShape(resolvedShape.resolvedId()),
        DAFNY_OUTPUT
      );
      if (
        AwsSdkNameResolverHelpers.isInAwsSdkNamespace(
          resolvedShape.resolvedId()
        )
      ) {
        Shape shape = subject.model.expectShape(resolvedShape.resolvedId());
        // TODO: Does this only work for AWS Services? It looks like that!.
        // On the bright side, `JavaLibrary.wrapAwsService` throws an error if its not service.
        return CodeBlock.of(
          "$L = $L",
          leftHand,
          JavaLibrary.wrapAwsService(
            shape,
            CodeBlock.of(NATIVE_OUTPUT),
            CodeBlock.of("null"),
            subject.sdkVersion
          )
        );
      }
      final Shape naiveShape = subject.model.expectShape(
        resolvedShape.naiveId()
      );
      final MethodReference toDafnyMethod =
        subject.toDafnyLibrary.conversionMethodReference(naiveShape);
      return CodeBlock.of(
        "$L = $L($L)",
        leftHand,
        toDafnyMethod.asNormalReference(),
        NATIVE_OUTPUT
      );
    }
  }

  private static TypeName preferDafnyInterface(
    final ResolvedShapeId resolvedShape,
    CodegenSubject subject
  ) {
    Shape shape = subject.model.expectShape(resolvedShape.resolvedId());
    if (shape.isServiceShape() || shape.isResourceShape()) {
      // If target is a Service or Resource,
      // the output type should be an interface.
      return subject.dafnyNameResolver.classNameForInterface(shape);
    }
    return subject.dafnyNameResolver.typeForShape(resolvedShape.resolvedId());
  }

  public static TypeName preferNativeInterface(
    final ResolvedShapeId resolvedShape,
    CodegenSubject subject
  ) {
    final Shape shape = subject.model.expectShape(resolvedShape.resolvedId());
    if (shape.isServiceShape() || shape.isResourceShape()) {
      // If target is a Service or Resource,
      // the output type should be an interface.
      return Native.classNameForInterfaceOrLocalService(
        shape,
        subject.sdkVersion
      );
    }
    return subject.nativeNameResolver.typeForShape(resolvedShape.resolvedId());
  }

  /** Generate a Method who's input and output are Idiomatic-Java.*/
  @SuppressWarnings("unused")
  public static class AsNative {
    // TODO: move
    //  software.amazon.polymorph.smithyjava.generator.library.ShimLibrary.operation
    //  and supporting methods here.

  }
}
