package software.amazon.polymorph.smithyjava.modeled;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeName;

import software.amazon.polymorph.smithyjava.MethodSignature;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.polymorph.smithyjava.generator.Generator;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.polymorph.smithyjava.generator.library.ShimLibrary;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;

import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.ModelUtils.ResolvedShapeId;

import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.Shape;

import static javax.lang.model.element.Modifier.PUBLIC;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.DAFNY_RESULT_CLASS_NAME;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.DAFNY_TUPLE0_CLASS_NAME;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.SMITHY_API_UNIT;

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
                CodegenSubject subject,
                ShimLibrary shimLibrary
        ) {
            final MethodSignature signature = methodSignature(operationShape, false, subject);
            final ResolvedShapeId inputResolved = signature.resolvedInput();
            final ResolvedShapeId outputResolved = signature.resolvedOutput();
            MethodSpec.Builder method = signature.method();
            final String operationName = operationShape.toShapeId().getName();
            // Convert Input
            method.addStatement(declareNativeInputAndCovert(inputResolved, subject, shimLibrary));
            // Try native implementation
            method.beginControlFlow("try");
            if (outputResolved.resolvedId().equals(SMITHY_API_UNIT)) {
                // if operation is void
                method
                        .addStatement(invoke(operationName))
                        .addStatement("return $T.create_Success($T.create())",
                                DAFNY_RESULT_CLASS_NAME, DAFNY_TUPLE0_CLASS_NAME);
            } else {
                // operation is not void
                method
                        .addStatement(declareNativeOutputAndInvoke(outputResolved, operationName, subject))
                        .addStatement(declareDafnyOutputAndConvert(outputResolved, subject, shimLibrary))
                        .addStatement("return $T.create_Success($L)",
                                DAFNY_RESULT_CLASS_NAME, DAFNY_OUTPUT);
            }
            // catch Errors in this Namespace
            method
                    .nextControlFlow("catch ($T ex)",
                            subject.nativeNameResolver.baseErrorForService())
                    .addStatement("return $T.create_Failure($T.Error(ex))",
                            DAFNY_RESULT_CLASS_NAME, shimLibrary.toDafnyClassName);
            // catch any Exception and cast them as an Opaque Error
            ClassName opaqueError = subject.nativeNameResolver.opaqueErrorForService();
            method
                    .nextControlFlow("catch ($T ex)", Exception.class)
                    .addStatement("$T error = $T.builder().obj(ex).cause(ex).build()",
                            opaqueError, opaqueError)
                    .addStatement("return $T.create_Failure($T.Error(error))",
                            DAFNY_RESULT_CLASS_NAME, shimLibrary.toDafnyClassName)
                    .endControlFlow();
            return method.build();
        }

        public static MethodSignature methodSignature(
                final OperationShape shape,
                boolean append_k,
                CodegenSubject subject
        ) {
            final ResolvedShapeId inputResolved = ModelUtils.resolveShape(
                    shape.getInputShape(), subject.model);
            final ResolvedShapeId outputResolved = ModelUtils.resolveShape(
                    shape.getOutputShape(), subject.model);
            final String operationName = append_k ?
                    // See JavaDoc on operation_K below
                    shape.toShapeId().getName() + "_k" :
                    shape.toShapeId().getName();
            final MethodSpec.Builder method = MethodSpec
                    .methodBuilder(operationName)
                    .addModifiers(PUBLIC);
            // if operation takes an argument
            if (!inputResolved.resolvedId().equals(SMITHY_API_UNIT)) {
                TypeName inputType = methodInputSignatureTypeName(inputResolved, subject);
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
            Shape shape = subject.model.expectShape(resolvedShape.resolvedId());
            if (shape.isServiceShape() || shape.isResourceShape()) {
                // If target is a Service or Resource,
                // the output type should be an interface OR LocalService.
                return subject.dafnyNameResolver.classNameForInterface(
                        subject.model.expectShape(resolvedShape.resolvedId()));
            }
            return subject.dafnyNameResolver.typeForShape(resolvedShape.resolvedId());
        }

        /** @return TypeName for a method's signature.*/
        static TypeName methodOutputTypeName(
                final ResolvedShapeId resolvedShape,
                CodegenSubject subject
        ) {
            Shape shape = subject.model.expectShape(resolvedShape.resolvedId());
            final TypeName success;
            if (shape.isServiceShape() || shape.isResourceShape()) {
                // If target is a Service or Resource,
                // the output type should be an interface.
                success = subject.dafnyNameResolver.classNameForInterface(
                        subject.model.expectShape(resolvedShape.resolvedId()));
            } else {
                success = subject.dafnyNameResolver.typeForShape(resolvedShape.resolvedId());
            }
            TypeName failure = subject.dafnyNameResolver.abstractClassForError();
            return Dafny.asDafnyResult(success, failure);
        }

        /** Declare the Idiomatic-Java input and
         * assign the conversion of the Dafny-Java object to it. */
        static CodeBlock declareNativeInputAndCovert(
                final ResolvedShapeId resolvedShape,
                CodegenSubject subject,
                ShimLibrary shimLibrary
        ) {
            return CodeBlock.of("$T $L = $T.$L($L)",
                    subject.nativeNameResolver.typeForShape(resolvedShape.resolvedId()),
                    NATIVE_INPUT,
                    shimLibrary.toNativeClassName,
                    resolvedShape.naiveId().getName(),
                    DAFNY_INPUT);
        }

        /** Declare the Idiomatic-Java output and
         * assign the result of the operation invocation to it. */
        static CodeBlock declareNativeOutputAndInvoke(
                final ResolvedShapeId resolvedShape,
                final String operationName,
                CodegenSubject subject
        ) {
            final TypeName nativeOutputType = subject.nativeNameResolver.typeForShape(resolvedShape.resolvedId());
            return CodeBlock.of("$T $L = $L",
                    nativeOutputType, NATIVE_OUTPUT,
                    invoke(operationName));
        }

        /** Invoke the operation. */
        static CodeBlock invoke(final String operationName) {
            return CodeBlock.of("this.$L.$L($L)",
                    Generator.INTERFACE_FIELD, operationName, NATIVE_INPUT);
        }

        /** Declare the Dafny-Java output and
         * assign the result of converting the Idiomatic-Java output to it. */
        static CodeBlock declareDafnyOutputAndConvert(
                final ResolvedShapeId resolvedShape,
                CodegenSubject subject,
                ShimLibrary shimLibrary
        ) {
            CodeBlock leftHand = CodeBlock.of("$T $L",
                    subject.dafnyNameResolver.typeForShape(resolvedShape.resolvedId()),
                    DAFNY_OUTPUT);
            if (AwsSdkNameResolverHelpers.isInAwsSdkNamespace(resolvedShape.resolvedId())) {
                Shape shape = subject.model.expectShape(resolvedShape.resolvedId());
                return CodeBlock.of("$L = $L",
                        leftHand,
                        JavaLibrary.wrapAwsService(shape, CodeBlock.of(NATIVE_OUTPUT), CodeBlock.of("null"), subject.sdkVersion));
            }
            return CodeBlock.of("$L = $T.$L($L)",
                    leftHand,
                    shimLibrary.toDafnyClassName,
                    resolvedShape.naiveId().getName(),
                    NATIVE_OUTPUT);
        }
    }

    /** Generate a Method who's input and output are Idiomatic-Java.*/
    @SuppressWarnings("unused")
    public static class AsNative {
        // TODO: move
        //  software.amazon.polymorph.smithyjava.generator.library.ShimLibrary.operation
        //  and supporting methods here.

    }


}
