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
        return null;
    }

    public static MethodSpec operationTest(
            final OperationShape operationShape,
            final SmokeTestCase testCase,
            JavaLibrary subject
    ) {
        MethodSpec.Builder method = methodSignature(testCase);
        final String operationName = operationShape.toShapeId().getName();
        // Try native implementation
        method.beginControlFlow("try");


        return method.build();
    }

    public static MethodSpec.Builder methodSignature(
            final SmokeTestCase testCase
    ) {
        // TODO: escape
        final String methodName = testCase.getId();
        return MethodSpec
                .methodBuilder(methodName)
                .addModifiers(PUBLIC)
                .returns(TypeName.VOID);
    }
}
