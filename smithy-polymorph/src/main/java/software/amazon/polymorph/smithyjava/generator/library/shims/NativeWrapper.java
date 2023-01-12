package software.amazon.polymorph.smithyjava.generator.library.shims;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeName;
import com.squareup.javapoet.TypeSpec;

import java.util.Set;

import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary.MethodSignature;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary.ResolvedShapeId;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.Shape;

import static javax.lang.model.element.Modifier.FINAL;
import static javax.lang.model.element.Modifier.PRIVATE;
import static javax.lang.model.element.Modifier.PUBLIC;
import static javax.lang.model.element.Modifier.STATIC;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.DAFNY_RESULT_CLASS_NAME;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.DAFNY_TUPLE0_CLASS_NAME;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.SMITHY_API_UNIT;

public class NativeWrapper extends ResourceShim {
    private static final String DAFNY_INPUT = "dafnyInput";
    private static final String NATIVE_INPUT = "nativeInput";
    private static final String NATIVE_OUTPUT = "nativeOutput";
    private static final String DAFNY_OUTPUT = "dafnyOutput";

    public static ClassName className(ClassName resourceClass) {
        return resourceClass.nestedClass("NativeWrapper");
    }

    public NativeWrapper(JavaLibrary javaLibrary, ResourceShape targetShape) {
        super(javaLibrary, targetShape);
    }

    @Override
    public Set<JavaFile> javaFiles() {
        throw new RuntimeException("NativeWrapper is a nested static class.");
    }

    TypeSpec nativeWrapper() {
        ClassName className = className();
        TypeSpec.Builder spec =TypeSpec
                .classBuilder(className)
                .addModifiers(PRIVATE, FINAL, STATIC)
                .addSuperinterface(Dafny.interfaceForResource(targetShape))
                .addField(interfaceName, INTERFACE_FIELD, PRIVATE, FINAL)
                .addMethod(nativeWrapperConstructor());
        getOperationsForTarget().forEach(oShape -> {
            spec.addMethod(operation(oShape));
            spec.addMethod(operation_K(oShape));
        });
        return spec.build();
    }

    private ClassName className() {
        return className(thisClassName);
    }

    MethodSpec nativeWrapperConstructor() {
        String paramName = "nativeImpl";
        return MethodSpec
                .constructorBuilder()
                .addParameter(interfaceName, paramName)
                .beginControlFlow("if ($L instanceof $T)",
                        paramName, subject.nativeNameResolver.typeForShape(targetShape.getId()))
                .addStatement("throw new $T($S)",
                        IllegalArgumentException.class,
                        "Recursive wrapping is strictly forbidden.")
                .endControlFlow()
                .addStatement("this.$L = $L", INTERFACE_FIELD, paramName)
                .build();
    }

    MethodSignature nativeWrapperOperationMethodSignature(
            final OperationShape shape,
            boolean append_k
    ) {
        final ResolvedShapeId inputResolved = subject.resolveShape(
                shape.getInputShape());
        final ResolvedShapeId outputResolved = subject.resolveShape(
                shape.getOutputShape());
        final String operationName = append_k ?
                shape.toShapeId().getName() + "_k" :
                shape.toShapeId().getName();
        final MethodSpec.Builder method = MethodSpec
                .methodBuilder(operationName)
                .addModifiers(PUBLIC);
        // if operation takes an argument
        if (!inputResolved.resolvedId().equals(SMITHY_API_UNIT)) {
            TypeName inputType = methodInputSignatureTypeName(inputResolved);
            method.addParameter(inputType, DAFNY_INPUT);
        }
        // if operation is not void
        if (!outputResolved.resolvedId().equals(SMITHY_API_UNIT)) {
            TypeName outputType = methodOutputTypeName(outputResolved);
            method.returns(outputType);
        }
        return new MethodSignature(method, inputResolved, outputResolved);
    }

    /** @return TypeName for a method's signature. */
    protected TypeName methodInputSignatureTypeName(ResolvedShapeId resolvedShape) {
        Shape shape = subject.model.expectShape(resolvedShape.resolvedId());
        if (shape.isServiceShape() || shape.isResourceShape()) {
            // If target is a Service or Resource,
            // the output type should be an interface OR LocalService.
            return subject.dafnyNameResolver.classNameForInterface(
                    subject.model.expectShape(resolvedShape.resolvedId()));
        }
        return subject.dafnyNameResolver.typeForShape(resolvedShape.resolvedId());
    }

    /** @return TypeName for a method's signature. */
    protected TypeName methodOutputTypeName(ResolvedShapeId resolvedShape) {
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

    @Override
    protected MethodSpec operation(OperationShape operationShape) {
        final MethodSignature signature = nativeWrapperOperationMethodSignature(operationShape, false);
        final ResolvedShapeId inputResolved = signature.resolvedInput();
        final ResolvedShapeId outputResolved = signature.resolvedOutput();
        MethodSpec.Builder method = signature.method();
        final String operationName = operationShape.toShapeId().getName();
        // Convert Input
        method.addStatement(nativeDeclareAndConvert(inputResolved));
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
            // TODO: Handle AWS Service/Resource edge case
            method
                    .addStatement(declareNativeOutputAndInvoke(outputResolved, operationName))
                    .addStatement(declareDafnyOutputAndConvert(outputResolved))
                    .addStatement("return $T.create_Success($L)",
                            DAFNY_RESULT_CLASS_NAME, DAFNY_OUTPUT);
        }
        // catch Errors in this Namespace
        method
                .nextControlFlow("catch ($T ex)",
                        subject.nativeNameResolver.baseErrorForService())
                .addStatement("return $T.create_Failure($T.Error(ex))",
                        DAFNY_RESULT_CLASS_NAME, toDafnyClassName);
        // catch any Exception and cast them as an Opaque Error
        ClassName opaqueError = subject.nativeNameResolver.opaqueErrorForService();
        method
                .nextControlFlow("catch ($T ex)", Exception.class)
                .addStatement("$T error = $T.builder().obj(ex).cause(ex).build()",
                        opaqueError, opaqueError)
                .addStatement("return $T.create_Failure($T.Error(error))",
                        DAFNY_RESULT_CLASS_NAME, toDafnyClassName)
                .endControlFlow();
        return method.build();
    }

    protected CodeBlock nativeDeclareAndConvert(ResolvedShapeId resolvedShape) {
        return CodeBlock.of("$T $L = $T.$L($L)",
                subject.nativeNameResolver.typeForShape(resolvedShape.resolvedId()),
                NATIVE_INPUT,
                toNativeClassName,
                resolvedShape.naiveId().getName(),
                DAFNY_INPUT);
    }

    protected CodeBlock declareNativeOutputAndInvoke(ResolvedShapeId resolvedShape, String operationName) {
        final TypeName nativeOutputType = subject.nativeNameResolver.typeForShape(resolvedShape.resolvedId());
        return CodeBlock.of("$T $L = $L",
                nativeOutputType, NATIVE_OUTPUT,
                invoke(operationName));
    }

    protected CodeBlock invoke(String operationName) {
      return CodeBlock.of("this.$L.$L($L)",
              INTERFACE_FIELD, operationName, NATIVE_INPUT);
    }

    protected CodeBlock declareDafnyOutputAndConvert(ResolvedShapeId resolvedShape) {
        return CodeBlock.of("$T $L = $T.$L($L)",
                subject.dafnyNameResolver.typeForShape(resolvedShape.resolvedId()),
                DAFNY_OUTPUT,
                toDafnyClassName,
                resolvedShape.naiveId().getName(),
                NATIVE_OUTPUT);
    }

    protected MethodSpec operation_K(OperationShape operationShape) {
        final MethodSignature signature = nativeWrapperOperationMethodSignature(operationShape, true);
        MethodSpec.Builder method = signature.method();
        method.addStatement("throw $T.builder().message($S).build()",
                subject.nativeNameResolver.baseErrorForService(),
                "Not supported at this time."
                );
        return method.build();
    }
}
