package software.amazon.polymorph.smithyjava.generator.library;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.ParameterizedTypeName;
import com.squareup.javapoet.TypeName;
import com.squareup.javapoet.TypeSpec;
import com.squareup.javapoet.WildcardTypeName;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import javax.lang.model.element.Modifier;

import dafny.DafnySequence;
import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.polymorph.smithyjava.generator.ToDafny;
import software.amazon.polymorph.smithyjava.unmodeled.CollectionOfErrors;
import software.amazon.polymorph.smithyjava.unmodeled.NativeError;
import software.amazon.polymorph.smithyjava.unmodeled.OpaqueError;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ShapeType;
import software.amazon.smithy.model.shapes.StructureShape;

import static software.amazon.smithy.utils.StringUtils.capitalize;
import static software.amazon.smithy.utils.StringUtils.uncapitalize;

/**
 * ToDafny is a helper class for the JavaLibrary's Shim.<p>
 * It holds methods to convert Native Java types to Dafny Java types.<p>
 */
public class ToDafnyLibrary extends ToDafny {
    // Hack to override CodegenSubject
    final JavaLibrary subject;
    final ClassName thisClassName;

    public ToDafnyLibrary(JavaLibrary javaLibrary) {
        super(javaLibrary);
        this.subject = javaLibrary;
        this.thisClassName = ClassName.get(subject.packageName, TO_DAFNY);
    }

    @Override
    public Set<JavaFile> javaFiles() {
        JavaFile.Builder builder = JavaFile
                .builder(thisClassName.packageName(), toDafny());
        return Collections.singleton(builder.build());
    }

    TypeSpec toDafny() {
        ArrayList<MethodSpec> toDafnyMethods = new ArrayList<>();
        // NativeError
        toDafnyMethods.add(nativeError());
        // OpaqueError
        toDafnyMethods.add(opaqueError());
        // CollectionError
        toDafnyMethods.add(collectionError());
        // Modeled exception classes
        subject.getErrorsInServiceNamespace().stream()
                .map(this::modeledError).forEachOrdered(toDafnyMethods::add);
        return TypeSpec.classBuilder(thisClassName)
                .addModifiers(Modifier.PUBLIC)
                .addMethods(toDafnyMethods)
                .build();
    }


    // Converts any subclass of NativeError to the correct Dafny Error,
    // or casts it as an OpaqueError.
    MethodSpec nativeError() {
        TypeName dafnyError = subject.dafnyNameResolver.getDafnyAbstractServiceError();
        ClassName nativeError = NativeError.className(subject.nativeNameResolver.modelPackage);
        MethodSpec.Builder method = MethodSpec.methodBuilder("Error")
                .returns(dafnyError)
                .addModifiers(PUBLIC_STATIC)
                .addParameter(nativeError, VAR_INPUT);
        List<ClassName> allErrors = subject.getErrorsInServiceNamespace().stream()
                .map(subject.nativeNameResolver::typeForStructure)
                .collect(Collectors.toCollection(ArrayList::new));
        allErrors.add(OpaqueError.className(subject.nativeNameResolver.modelPackage));
        allErrors.add(CollectionOfErrors.className(subject.nativeNameResolver.modelPackage));
        allErrors.forEach(errorClassName ->
                method.beginControlFlow("if ($L instanceof $T)", VAR_INPUT, errorClassName)
                        .addStatement("return $T.Error(($T) $L)", thisClassName, errorClassName, VAR_INPUT)
                        .endControlFlow()
        );
        return method
                .addStatement("return $T.create_Opaque($L)", dafnyError, VAR_INPUT)
                .build();
    }

    MethodSpec opaqueError() {
        TypeName dafnyError = subject.dafnyNameResolver.getDafnyAbstractServiceError();
        ClassName opaqueError = OpaqueError.className(subject.nativeNameResolver.modelPackage);
        return MethodSpec.methodBuilder("Error")
                .returns(dafnyError)
                .addModifiers(PUBLIC_STATIC)
                .addParameter(opaqueError, VAR_INPUT)
                .addStatement("return $T.create_Opaque($L.obj())", dafnyError, VAR_INPUT)
                .build();
    }

    MethodSpec collectionError() {
        ClassName dafnyError = subject.dafnyNameResolver.getDafnyAbstractServiceError();
        ClassName collectionError = CollectionOfErrors.className(subject.nativeNameResolver.modelPackage);
        ParameterizedTypeName listArg = ParameterizedTypeName.get(
                ClassName.get(DafnySequence.class),
                WildcardTypeName.subtypeOf(dafnyError)
        );
        CodeBlock genericCall = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(ShapeType.LIST).asNormalReference();
        MethodReference getTypeDescriptor = new MethodReference(
                dafnyError,
                "_typeDescriptor");
        return MethodSpec.methodBuilder("Error")
                .returns(dafnyError)
                .addModifiers(PUBLIC_STATIC)
                .addParameter(collectionError, VAR_INPUT)
                .addStatement(
                        "$T list = $L(\n$L.list(), \n$T::Error, \n$L())",
                        listArg, genericCall, VAR_INPUT, thisClassName, getTypeDescriptor.asNormalReference()
                        )
                .addStatement("return $T.create_Collection(list)", dafnyError)
                .build();
    }

    /** For Library structure members, the getter is `un-capitalized member name`. */
    @Override
    protected CodeBlock getMember(CodeBlock variableName, MemberShape memberShape) {
        return CodeBlock.of("$L.$L()", variableName, uncapitalize(memberShape.getMemberName()));
    }
}
