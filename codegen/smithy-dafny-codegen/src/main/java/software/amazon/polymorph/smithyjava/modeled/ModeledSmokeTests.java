package software.amazon.polymorph.smithyjava.modeled;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeName;
import software.amazon.polymorph.smithyjava.MethodSignature;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.polymorph.smithyjava.generator.library.ShimLibrary;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.smoketests.traits.SmokeTestCase;

import static javax.lang.model.element.Modifier.PUBLIC;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.DAFNY_TUPLE0_CLASS_NAME;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.SMITHY_API_UNIT;

public class ModeledSmokeTests {

    public static JavaFile javaFile(String packageName, OperationShape operationShape, JavaLibrary subject) {

    }

    public static MethodSpec operationTest(
            final OperationShape operationShape,
            final SmokeTestCase testCase,
            JavaLibrary subject
    ) {
        final MethodSignature signature = methodSignature(testCase);
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
            final SmokeTestCase testCase
    ) {
        // TODO: escape
        final String methodName = testCase.getId();
        final MethodSpec.Builder method = MethodSpec
                .methodBuilder(methodName)
                .addModifiers(PUBLIC)
                .returns(TypeName.VOID);
        return new MethodSignature(method, inputResolved, outputResolved);
    }
}
