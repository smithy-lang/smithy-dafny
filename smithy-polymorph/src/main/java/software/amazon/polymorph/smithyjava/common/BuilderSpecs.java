package software.amazon.polymorph.smithyjava.common;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.FieldSpec;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeSpec;

import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import javax.lang.model.element.Modifier;

import software.amazon.polymorph.smithyjava.nameresolver.NameResolver;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.StructureShape;

import static javax.lang.model.element.Modifier.ABSTRACT;
import static javax.lang.model.element.Modifier.PROTECTED;
import static javax.lang.model.element.Modifier.PUBLIC;
import static javax.lang.model.element.Modifier.STATIC;

public class BuilderSpecs {
    public static String BUILDER_VAR = "builder";

    @Nonnull private final ClassName className;
    @Nullable private final ClassName superName;
    @Nonnull private final List<FieldSpec> localFields;
    @Nonnull private final List<FieldSpec> superFields;

    BuilderSpecs(
            @Nonnull String packageName,
            @Nonnull StructureShape classShape,
            @Nullable StructureShape superShape,
            @Nonnull NameResolver nameResolver
    ) {
        this.className = ClassName.get(packageName, classShape.getId().getName());
        Set<String> superFieldNames;
        if (superShape != null) {
            this.superName = ClassName.get(packageName, superShape.getId().getName());
            this.superFields = superShape.members().stream()
                    .map(shape -> fieldSpecFromMemberShape(shape, nameResolver))
                    .collect(Collectors.toList());
            superFieldNames = this.superFields.stream()
                    .map(field -> field.name)
                    .collect(Collectors.toSet());
        } else {
            this.superName = null;
            this.superFields = Collections.emptyList();
            superFieldNames = Collections.emptySet();
        }
        this.localFields = classShape.members().stream()
                // check the local field Name is not contained by Super Fields
                .filter(shape -> !superFieldNames.contains(shape.getMemberName()))
                .map(shape -> fieldSpecFromMemberShape(shape, nameResolver))
                .collect(Collectors.toList());
    }

    BuilderSpecs(
            @Nonnull ClassName className,
            @Nullable ClassName superName,
            @Nonnull List<FieldSpec> localFields,
            @Nonnull List<FieldSpec> superFields
    ) {
        this.className = className;
        this.superName = superName;
        this.localFields = localFields;
        this.superFields = superFields;
    }

    static FieldSpec fieldSpecFromMemberShape(
            MemberShape memberShape,
            NameResolver nameResolver
    ) {
        return FieldSpec.builder(
                nameResolver.typeForShape(memberShape.getTarget().toShapeId()),
                memberShape.getMemberName())
                .build();
    }

    static ClassName builderInterfaceName(ClassName aClassName) {
        return aClassName.nestedClass("Builder");
    }

    static ClassName builderImplName(ClassName aClassName) {
        return aClassName.nestedClass("BuilderImpl");
    }

    ClassName builderInterfaceName() { return builderInterfaceName(className); }

    ClassName builderImplName() { return builderImplName(className); }

    TypeSpec builderInterface() {
        TypeSpec.Builder builder = TypeSpec
                .interfaceBuilder(builderInterfaceName());
        if (superName != null) { builder.addSuperinterface(builderInterfaceName(superName)); }
        superFields.forEach(field ->
                builder.addMethod(MethodSpec.methodBuilder(field.name)
                        .addParameter(field.type, field.name)
                        .returns(builderInterfaceName())
                        .addModifiers(ABSTRACT, PUBLIC)
                        .build())
        );
        localFields.forEach(
                field -> {
                    builder.addMethod(
                            MethodSpec.methodBuilder(field.name)
                                    .addParameter(field.type, field.name)
                                    .returns(builderInterfaceName())
                                    .addModifiers(PUBLIC, ABSTRACT)
                                    .build());
                    builder.addMethod(
                            MethodSpec.methodBuilder(field.name)
                                    .returns(field.type)
                                    .addModifiers(PUBLIC, ABSTRACT)
                                    .build());
                });
        return builder.addMethod(MethodSpec.methodBuilder("build")
                        .returns(className)
                        .addModifiers(PUBLIC, ABSTRACT)
                        .build())
                .build();
    }

    TypeSpec builderImpl(boolean overrideSuper) {
        return builderImpl(overrideSuper, null);
    }

    TypeSpec builderImpl(boolean overrideSuper, MethodSpec modelConstructor) {
        if (overrideSuper && superName == null) {
            throw new IllegalArgumentException("Cannot overrideSuper if there is no super");
        }
        TypeSpec.Builder builder = TypeSpec
                .classBuilder(builderImplName())
                .addSuperinterface(builderInterfaceName())
                .addModifiers(STATIC, PROTECTED);
        if (superName != null) { builder.superclass(builderImplName(superName)); }
        // Add Fields
        localFields.forEach(field ->
                builder.addField(field.type, field.name, PROTECTED));
        // Add Constructors
        builder.addMethod(MethodSpec.constructorBuilder()
                .addModifiers(PROTECTED)
                .build());
        if (modelConstructor == null) {
            MethodSpec.Builder _modelConstructor = MethodSpec
                    .constructorBuilder()
                    .addModifiers(PROTECTED)
                    .addParameter(className, "model");
            if (superName != null ) { _modelConstructor.addStatement("super(model)"); }
            localFields.forEach(field ->
                    _modelConstructor.addStatement(
                            "this.$L = model.$L()", field.name, field.name)
            );
            builder.addMethod(_modelConstructor.build());
        } else {
            builder.addMethod(modelConstructor);
        }
        // for local fields
        localFields.forEach(field -> {
            // Builder Setter Method
            builder.addMethod(MethodSpec
                    .methodBuilder(field.name)
                    .addModifiers(Modifier.PUBLIC)
                    .returns(builderInterfaceName())
                    .addParameter(field.type, field.name)
                    .addStatement("this.$L = $L", field.name, field.name)
                    .addStatement("return this")
                    .build());
            // Getter Method
            builder.addMethod(MethodSpec
                    .methodBuilder(field.name)
                    .addModifiers(Modifier.PUBLIC)
                    .returns(field.type)
                    .addStatement("return this.$L", field.name)
                    .build());
        });
        // Builder for super's fields
        superFields.forEach(field -> {
            MethodSpec.Builder method = MethodSpec
                    .methodBuilder(field.name)
                    .returns(builderInterfaceName())
                    .addModifiers(Modifier.PUBLIC)
                    .addParameter(field.type, field.name)
                    .addStatement("super.$L($L)", field.name, field.name)
                    .addStatement("return this");
            if (overrideSuper) { method.addAnnotation(Override.class); }
            builder.addMethod(method.build());
        });
        // build
        MethodSpec.Builder buildMethod = MethodSpec
                .methodBuilder("build")
                .addModifiers(Modifier.PUBLIC)
                .returns(className)
                .addStatement("return new $T(this)", className);
        if (overrideSuper) { buildMethod.addAnnotation(Override.class); }
        builder.addMethod(buildMethod.build());
        return builder.build();
    }

    MethodSpec toBuilderMethod(boolean override) {
        MethodSpec.Builder method = MethodSpec
                .methodBuilder("toBuilder")
                .addModifiers(PUBLIC)
                .returns(builderInterfaceName())
                .addStatement("return new $T(this)", builderImplName());
        if (override) {
            method.addAnnotation(Override.class);
        }
        return method.build();
    }

    MethodSpec builderMethod() {
        MethodSpec.Builder method = MethodSpec
                .methodBuilder("builder")
                .addModifiers(PUBLIC, STATIC)
                .returns(builderInterfaceName())
                .addStatement("return new $T()", builderImplName());
        return method.build();
    }
}
