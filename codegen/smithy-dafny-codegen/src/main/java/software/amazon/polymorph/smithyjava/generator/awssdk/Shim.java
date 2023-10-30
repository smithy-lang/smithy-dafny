package software.amazon.polymorph.smithyjava.generator.awssdk;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeName;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.polymorph.smithyjava.generator.Generator;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.smithy.model.shapes.ShapeType;

import static javax.lang.model.element.Modifier.PUBLIC;
import static javax.lang.model.element.Modifier.STATIC;

public abstract class Shim extends Generator {
    public Shim(CodegenSubject subject) {
        super(subject);
    }

    protected MethodSpec successOfClientConstructor() {
        ClassName clientType = subject.dafnyNameResolver.classNameForInterface(subject.serviceShape);
        MethodSpec.Builder method = MethodSpec
                .methodBuilder("createSuccessOfClient")
                .addModifiers(STATIC, PUBLIC)
                .addParameter(clientType, "client")
                .returns(Dafny.asDafnyResult(
                        clientType,
                        subject.dafnyNameResolver.abstractClassForError()
                ));
        method.addStatement("return $L",
                subject.dafnyNameResolver.createSuccess(
                        subject.dafnyNameResolver.typeDescriptor(subject.serviceShape.toShapeId()),
                        CodeBlock.of("client")));
        return method.build();
    }

    protected MethodSpec failureOfExceptionConstructor() {
        ClassName clientType = subject.dafnyNameResolver.classNameForInterface(subject.serviceShape);
        MethodSpec.Builder method = MethodSpec
                .methodBuilder("createFailureOfException")
                .addModifiers(STATIC, PUBLIC)
                .addParameter(ClassName.get(Exception.class), "exception")
                .returns(Dafny.asDafnyResult(
                        clientType,
                        subject.dafnyNameResolver.abstractClassForError()
                ));
        CodeBlock stringTypeDescriptor = Dafny.TYPE_DESCRIPTOR_BY_SHAPE_TYPE.get(ShapeType.STRING);
        method.addStatement("Error dafny_error = Error.create_InternalServerError($L)",
                subject.dafnyNameResolver.createSome(stringTypeDescriptor,
                        CodeBlock.of("CharacterSequence(exception.getMessage())")));
        method.addStatement("return $L",
                subject.dafnyNameResolver.createFailure(
                        subject.dafnyNameResolver.typeDescriptor(subject.serviceShape.toShapeId()),
                        CodeBlock.of("dafny_error")));
        return method.build();
    }

    protected MethodSpec booleanSomeConstructor() {
        TypeName booleanType = TypeName.BOOLEAN.box();
        MethodSpec.Builder method = MethodSpec
                .methodBuilder("createBooleanSome")
                .addModifiers(STATIC, PUBLIC)
                .addParameter(booleanType, "b")
                .returns(Dafny.asDafnyOption(
                        booleanType
                ));
        method.addStatement("return $L",
                subject.dafnyNameResolver.createSome(
                        subject.dafnyNameResolver.TYPE_DESCRIPTOR_BY_SHAPE_TYPE.get(ShapeType.BOOLEAN),
                        CodeBlock.of("b")));
        return method.build();
    }

    protected MethodSpec booleanNoneConstructor() {
        TypeName booleanType = TypeName.BOOLEAN.box();
        MethodSpec.Builder method = MethodSpec
                .methodBuilder("createBooleanNone")
                .addModifiers(STATIC, PUBLIC)
                .returns(Dafny.asDafnyOption(
                        booleanType
                ));
        method.addStatement("return $L",
                subject.dafnyNameResolver.createNone(
                        subject.dafnyNameResolver.TYPE_DESCRIPTOR_BY_SHAPE_TYPE.get(ShapeType.BOOLEAN)));
        return method.build();
    }
}
