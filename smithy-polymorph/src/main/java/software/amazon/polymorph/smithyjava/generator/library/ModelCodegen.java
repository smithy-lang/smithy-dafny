package software.amazon.polymorph.smithyjava.generator.library;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeName;
import com.squareup.javapoet.TypeSpec;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;

import javax.lang.model.element.Modifier;

import software.amazon.polymorph.smithyjava.common.NativeError;
import software.amazon.polymorph.smithyjava.common.OpaqueError;
import software.amazon.polymorph.smithyjava.generator.Generator;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.utils.StringUtils;


class ModelCodegen extends Generator {

    /** Public Java Interfaces will go here. */
    public final String packageName;
    /** Public POJOs will go here. */
    public final String modelPackageName;

    public ModelCodegen(Library subject) {
        super(subject);
        packageName = subject.packageName;
        modelPackageName = subject.modelPackageName;
    }

    @Override
    public LinkedHashSet<JavaFile> javaFiles() {
        LinkedHashSet<JavaFile> rtn = new LinkedHashSet<>();
        // NativeError Exception Class
        rtn.add(NativeError.javaFile(modelPackageName));
        // Opaque Exception Class
        rtn.add(OpaqueError.javaFile(modelPackageName));
        // Collection of Errors class
        /*rtn.add(CollectionOfErrors(modelPackageName));*/
        // Modeled exception classes
        /*subject.model.getStructureShapes().stream()
                .filter(shape -> shape.hasTrait(ErrorTrait.class))
                .filter(shape -> ModelUtils.isInServiceNamespace(shape.getId(), subject.serviceShape))
                .map(this::modeledException).forEachOrdered(rtn::add);*/
        // Structures
        /*subject.model.getStructureShapes().stream()
                .filter(Generator::shouldGenerateStructure)
                .filter(shape -> ModelUtils.isInServiceNamespace(shape.getId(), subject.serviceShape))
                .map(this::generateStructure).forEachOrdered(rtn::add);
        // Enums
        subject.model.getStringShapesWithTrait(EnumTrait.class).stream()
                .filter(shape -> ModelUtils.isInServiceNamespace(shape.getId(), subject.serviceShape))
                .map(this::generateEnum).forEachOrdered(rtn::add);
        // Resources
        subject.model.getResourceShapes().stream()
                .filter(shape -> ModelUtils.isInServiceNamespace(shape.getId(), subject.serviceShape))
                .forEachOrdered(shape -> {
                    rtn.add(generateResourceInterface(shape));
                    rtn.add(generateResourceClass(shape));
                    if (shape.hasTrait(ExtendableTrait.class)) {
                        rtn.add(generateNativeWrapper(shape));
                    }
                });*/
        return rtn;
    }

    JavaFile modeledException(StructureShape shape) {
        /*TypeSpec.Builder spec = TypeSpec
                .classBuilder(ClassName.get(modelPackageName, shape.getId().getName()))
                .addModifiers(Modifier.PUBLIC)
                .superclass(ClassName.get(modelPackageName, NATIVE_ERROR));
        List<MemberShape> requiredArgs = new ArrayList<>();
        shape.getAllMembers().forEach((name, memberShape) -> {
            TypeName fieldType = subject.nativeNameResolver.typeForShape(memberShape.getId());
            String fieldName = StringUtils.lowerCase(name);
            spec.addField(fieldType, fieldName);
            if (memberShape.isRequired()) {
                requiredArgs.add(memberShape);
            }
            // getter method
            spec.addMethod(
                    MethodSpec.methodBuilder(getFieldMethodName(memberShape))
                            .addModifiers(Modifier.PUBLIC)
                            .returns(fieldType)
                            .addCode("return this.$L", fieldName)
                            .build());
            // setter method
            spec.addMethod(
                    MethodSpec.methodBuilder(setFieldMethodName(memberShape))
                            .addModifiers(Modifier.PUBLIC)
                            .addParameter(fieldType, fieldName)
                            .addCode("this.$L = $L", fieldName, fieldName)
                            .build());
        });*/

        /*        .addMethod(MethodSpec.constructorBuilder()
                        .addParameter(String.class, "message")
                        .addCode("super(message)").build())
                .build();*/
        /*return JavaFile.builder(modelPackageName, spec).build();*/
        return null;
    }

    static String getFieldMethodName(MemberShape shape) {
        return "get" + StringUtils.capitalize(shape.getMemberName());
    }

    static String setFieldMethodName(MemberShape shape) {
        return "set" + StringUtils.capitalize(shape.getMemberName());
    }

    JavaFile generateStructure(StructureShape structureShape) {
        throw new RuntimeException("TODO");
    }

    JavaFile generateEnum(StringShape stringShape) {
        throw new RuntimeException("TODO");
    }

    JavaFile generateResourceInterface(ResourceShape shape) {
        throw new RuntimeException("TODO");
    }

    JavaFile generateResourceClass(ResourceShape shape) {
        throw new RuntimeException("TODO");
    }

    JavaFile generateNativeWrapper(ResourceShape shape) {
        throw new RuntimeException("TODO");
    }
}
