package software.amazon.polymorph.smithyjava.generator.library;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeName;
import com.squareup.javapoet.TypeSpec;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import javax.lang.model.element.Modifier;

import software.amazon.polymorph.smithyjava.generator.ToNative;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.smithyjava.unmodeled.CollectionOfErrors;
import software.amazon.polymorph.smithyjava.unmodeled.NativeError;
import software.amazon.polymorph.smithyjava.unmodeled.OpaqueError;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeType;

/**
 * ToNative is a helper class for the JavaLibrary's Shim.<p>
 * It holds methods to convert Dafny Java types to Native Java types.<p>
 */
public class ToNativeLibrary extends ToNative {
    // Hack to override CodegenSubject
    final JavaLibrary subject;

    public ToNativeLibrary(JavaLibrary javaLibrary) {
        super(javaLibrary, ClassName.get(javaLibrary.packageName, TO_NATIVE));
        this.subject = javaLibrary;
    }

    @Override
    public Set<JavaFile> javaFiles() {
        JavaFile.Builder builder = JavaFile
                .builder(thisClassName.packageName(), toNative());
        return Collections.singleton(builder.build());
    }

    TypeSpec toNative() {
        ArrayList<MethodSpec> toNativeMethods = new ArrayList<>();
        // NativeError is skipped as there is no Dafny allegory of NativeError
        // OpaqueError
        toNativeMethods.add(opaqueError());
        // CollectionError
        toNativeMethods.add(collectionError());
        // Any Error
        toNativeMethods.add(dafnyError());
        // Enums
        subject.getEnumsInServiceNamespace().stream()
                .map(this::modeledEnum).forEachOrdered(toNativeMethods::add);
        return TypeSpec.classBuilder(thisClassName)
                .addModifiers(Modifier.PUBLIC)
                .addMethods(toNativeMethods)
                .build();
    }

    MethodSpec opaqueError() {
        ClassName inputType = subject.dafnyNameResolver.classForDatatypeConstructor("Error", "Opaque");
        ClassName returnType = OpaqueError.nativeClassName(subject.modelPackageName);
        MethodSpec.Builder method = super.initializeErrorMethodSpec(inputType, returnType);
        method = super.createNativeBuilder(method, returnType);
        // Set Value
        method.addStatement("$L.obj($L.dtor_obj())", NATIVE_BUILDER, VAR_INPUT);
        // Build and Return
        return super.buildAndReturn(method);
    }

    MethodSpec collectionError() {
        ClassName inputType = subject.dafnyNameResolver.classForDatatypeConstructor("Error", "Collection");
        ClassName returnType = CollectionOfErrors.nativeClassName(subject.modelPackageName);
        CodeBlock genericCall = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(ShapeType.LIST).asNormalReference();
        MethodSpec.Builder method = super.initializeErrorMethodSpec(inputType, returnType);
        super.createNativeBuilder(method, returnType);
        // Set Value
        method.addStatement("$L.list(\n$L(\n$L.dtor_list(), \n$T::Error))",
                NATIVE_BUILDER, genericCall, VAR_INPUT, thisClassName);
        // Build and Return
        return super.buildAndReturn(method);
    }

    MethodSpec dafnyError() {
        ClassName inputType = subject.dafnyNameResolver.classForError();
        ClassName returnType = NativeError.nativeClassName(subject.modelPackageName);
        MethodSpec.Builder method = super.initializeErrorMethodSpec(inputType, returnType);
        // Ok... this is silly complicated... but:
        // we need a list of `<datatypeConstructor>`,
        // but we only have the logic exposed to look up the TypeName,
        // which, as a string, will be <modelPackage>.Error_<datatypeConstructor>,
        // so we "cast that" to a class name
        // (which is valid, as Dafny does generate a class for these)
        // and get just the "simpleName" (i.e.: Error_<datatypeConstructor>)
        // and, finally, replace "Error_" with nothing, thus getting just "<datatypeConstructor>".
        List<String> allDafnyErrorConstructors = subject.getErrorsInServiceNamespace().stream()
                .map(Shape::getId)
                .map(subject.dafnyNameResolver::typeForShape)
                .map(TypeName::toString)
                .map(typeName -> ClassName.bestGuess(typeName).simpleName())
                .map(simpleName -> simpleName.replaceFirst("Error_", ""))
                .collect(Collectors.toCollection(ArrayList::new));
        allDafnyErrorConstructors.add("Opaque");
        allDafnyErrorConstructors.add("Collection");
        allDafnyErrorConstructors.forEach(constructorName -> method.beginControlFlow("if ($L.$L())", VAR_INPUT, Dafny.datatypeConstructorIs(constructorName))
                .addStatement("return $T.Error(($T) $L)", thisClassName, subject.dafnyNameResolver.classForDatatypeConstructor("Error", constructorName), VAR_INPUT)
                .endControlFlow()
        );
        // If the Error cannot be placed into one of the above, call it opaque and move on
        super.createNativeBuilder(method, OpaqueError.nativeClassName(subject.modelPackageName));
        method.addStatement("$L.obj($L)", NATIVE_BUILDER, VAR_INPUT);
        return super.buildAndReturn(method);
    }
}
