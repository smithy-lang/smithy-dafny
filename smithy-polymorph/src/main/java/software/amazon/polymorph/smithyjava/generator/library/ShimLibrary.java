package software.amazon.polymorph.smithyjava.generator.library;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.FieldSpec;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeName;

import java.util.List;

import software.amazon.polymorph.smithyjava.generator.Generator;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary.ResolvedShapeId;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;

import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;

import static javax.lang.model.element.Modifier.PUBLIC;
import static software.amazon.polymorph.smithyjava.NamespaceHelper.AWS_SERVICE_NAMESPACE_PREFIX;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.DAFNY_TUPLE0_CLASS_NAME;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.SMITHY_API_UNIT;

/**
 * A Java Library's Shim is the public class
 * that consumers interact with in Native Java.<p>
 * ShimLibrary holds the logic required to generate the Shim.
 */
public abstract class ShimLibrary extends Generator {
    protected static final String DAFNY_INTERFACE_FIELD = "_impl";
    protected static final String NATIVE_VAR = "nativeValue";
    protected static final String DAFNY_VAR = "dafnyValue";
    protected static final String RESULT_VAR = "result";
    // Hack to override CodegenSubject
    // See ModelCodegen for explanation
    protected final JavaLibrary subject;
    /** The class name of the Subject's ToDafny class. */
    protected final ClassName toDafnyClassName;
    /** The class name of the Subject's ToNative class. */
    protected final ClassName toNativeClassName;

    public ShimLibrary(JavaLibrary javaLibrary) {
        super(javaLibrary);
        this.subject = javaLibrary;
        this.toDafnyClassName = ToDafnyLibrary.className(javaLibrary);
        this.toNativeClassName = ToNativeLibrary.className(javaLibrary);
    }

    protected abstract List<OperationShape> getOperationsForTarget();

    protected abstract MethodSpec impl();

    protected abstract FieldSpec getField();

    protected JavaLibrary.MethodSignature operationMethodSignature(OperationShape operationShape) {
        final ResolvedShapeId inputResolved = subject.resolveShape(
                operationShape.getInputShape());
        final ResolvedShapeId outputResolved = subject.resolveShape(
                operationShape.getOutputShape());
        final String operationName = operationShape.toShapeId().getName();
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
        return new JavaLibrary.MethodSignature(method, inputResolved, outputResolved);
    }

    /** @return TypeName for a method's signature. */
    private TypeName methodSignatureTypeName(ResolvedShapeId resolvedShape) {
        Shape shape = subject.model.expectShape(resolvedShape.resolvedId());
        if (shape.isServiceShape() || shape.isResourceShape()) {
            // If target is a Service or Resource,
            // the output type should be an interface OR LocalService.
            return subject.nativeNameResolver.classNameForInterfaceOrLocalService(
                    subject.model.expectShape(resolvedShape.resolvedId()));
        }
        return subject.nativeNameResolver.typeForShape(resolvedShape.resolvedId());
    }

    protected MethodSpec operation(OperationShape operationShape) {
        final JavaLibrary.MethodSignature signature = operationMethodSignature(operationShape);
        final ResolvedShapeId inputResolved = signature.resolvedInput();
        final ResolvedShapeId outputResolved = signature.resolvedOutput();
        MethodSpec.Builder method = signature.method();
        final String operationName = operationShape.toShapeId().getName();
        // if operation takes an argument
        if (!inputResolved.resolvedId().equals(SMITHY_API_UNIT)) {
            // If input is a Service or Resource,
            Shape shape = subject.model.expectShape(inputResolved.resolvedId());
            if (shape.isServiceShape() || shape.isResourceShape()) {
                if (inputResolved.resolvedId().getNamespace().startsWith(AWS_SERVICE_NAMESPACE_PREFIX)) {
                    // if operation takes an AWS Service/Resource, just pass to dafny
                    method.addStatement(dafnyDeclare(inputResolved.resolvedId()));
                } else {
                    // if operation takes a non-AWS Service/Resource, get impl()
                    method.addStatement(dafnyDeclareGetImpl(inputResolved.resolvedId()));
                }
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
            success = subject.dafnyNameResolver.typeForShape(outputResolved.resolvedId());
        }
        TypeName failure = subject.dafnyNameResolver.abstractClassForError();
        //TODO: handle operation specific errors?
        TypeName result = Dafny.asDafnyResult(success, failure);
        // if operation takes an argument
        if (!inputResolved.resolvedId().equals(SMITHY_API_UNIT)) {
            // call with that argument in dafny
            method.addStatement("$T $L = this.$L.$L($L)",
                    result, RESULT_VAR,
                    DAFNY_INTERFACE_FIELD, operationName, DAFNY_VAR);
        } else {
            // call with no args
            method.addStatement("$T $L = this.$L.$L()",
                    result, RESULT_VAR,
                    DAFNY_INTERFACE_FIELD, operationName);
        }
        // Handle Failure
        method.addCode(ifFailure());

        // if operation is void
        if (outputResolved.resolvedId().equals(SMITHY_API_UNIT)) {
            return method.build();
        }
        Shape outputShape = subject.model.expectShape(outputResolved.resolvedId());
        // if resolvedOutput is a Service or Resource
        if (outputShape.isServiceShape() || outputShape.isResourceShape()) {
            if (outputResolved.resolvedId().getNamespace().startsWith(AWS_SERVICE_NAMESPACE_PREFIX)) {
                // if operation outputs an AWS Service/Resource, just return the Dafny result
                method.addStatement("return $L.dtor_value()", RESULT_VAR);
            } else {
                // if operation outputs a non-AWS Service/Resource, wrap result with Shim
                method.addStatement("return $L",
                        subject.wrapWithShim(outputResolved.resolvedId(),
                        CodeBlock.of("$L.dtor_value()", RESULT_VAR)));
            }
            return method.build();
        }
        // else convert success to native and return
        method.addStatement("return $T.$L($L.dtor_value())",
                toNativeClassName, outputResolved.naiveId().getName(), RESULT_VAR);
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
        final ShapeId shapeId = resolvedShape.naiveId();
        return CodeBlock.of("$T $L = $T.$L($L)",
                subject.dafnyNameResolver.typeForShape(targetId),
                DAFNY_VAR,
                toDafnyClassName,
                shapeId.getName(),
                NATIVE_VAR);
    }

    // Reference also adds a complication,
    // as they do not need to be converted.
    protected CodeBlock dafnyDeclare(ShapeId targetId) {
        return CodeBlock.of("$T $L = $L",
                subject.dafnyNameResolver.typeForShape(targetId),
                DAFNY_VAR,
                NATIVE_VAR);
    }

    protected CodeBlock dafnyDeclareGetImpl(ShapeId targetId) {
        return CodeBlock.of("$L.impl()", dafnyDeclare(targetId));
    }

    protected CodeBlock ifFailure() {
        return CodeBlock.builder()
                .beginControlFlow("if ($L.is_Failure())", RESULT_VAR)
                .addStatement("throw $T.Error($L.dtor_error())",
                        toNativeClassName, RESULT_VAR)
                .endControlFlow()
                .build();
    }
}
