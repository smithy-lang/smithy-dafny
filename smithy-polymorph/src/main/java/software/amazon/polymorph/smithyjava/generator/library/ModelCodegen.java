package software.amazon.polymorph.smithyjava.generator.library;

import com.squareup.javapoet.JavaFile;

import java.util.LinkedHashSet;
import java.util.List;

import software.amazon.polymorph.smithyjava.modeled.ModeledEnum;
import software.amazon.polymorph.smithyjava.modeled.ModeledError;
import software.amazon.polymorph.smithyjava.modeled.ModeledStructure;
import software.amazon.polymorph.smithyjava.unmodeled.CollectionOfErrors;
import software.amazon.polymorph.smithyjava.unmodeled.NativeError;
import software.amazon.polymorph.smithyjava.unmodeled.OpaqueError;
import software.amazon.polymorph.smithyjava.generator.Generator;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.TraitDefinition;


class ModelCodegen extends Generator {

    /** Public Java Interfaces will go here. */
    public final String packageName;
    /** Public POJOs will go here. */
    public final String modelPackageName;

    public ModelCodegen(JavaLibrary subject) {
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
        rtn.add(CollectionOfErrors.javaFile(modelPackageName));
        // Modeled exception classes
        getErrorsInServiceNamespace().stream()
                .map(this::modeledError).forEachOrdered(rtn::add);
        // Structures
        getStructuresInServiceNamespace().stream()
                .map(this::modeledStructure).forEachOrdered(rtn::add);
        // Enums
        getEnumsInServiceNamespace().stream()
                .map(this::modeledEnum).forEachOrdered(rtn::add);
        // Resources
        /*subject.model.getResourceShapes().stream()
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

    List<StructureShape> getErrorsInServiceNamespace() {
        return subject.model.getStructureShapes().stream()
                .filter(shape -> shape.hasTrait(ErrorTrait.class))
                .filter(shape -> ModelUtils.isInServiceNamespace(shape.getId(), subject.serviceShape))
                .toList();
    }

    JavaFile modeledError(StructureShape shape) {
        return ModeledError.javaFile(modelPackageName, shape, subject);
    }

    List<StructureShape> getStructuresInServiceNamespace() {
        return subject.model.getStructureShapes().stream()
                .filter(shape -> !shape.hasTrait(ErrorTrait.class))
                .filter(shape -> !shape.hasTrait(TraitDefinition.class))
                .filter(shape -> !shape.hasTrait(EnumTrait.class))
                .filter(shape -> ModelUtils.isInServiceNamespace(shape.getId(), subject.serviceShape))
                .toList();
    }

    JavaFile modeledStructure(StructureShape shape) {
        return ModeledStructure.javaFile(modelPackageName, shape, subject);
    }

    List<StringShape> getEnumsInServiceNamespace() {
        return subject.model.getStringShapesWithTrait(EnumTrait.class).stream()
                .filter(shape -> ModelUtils.isInServiceNamespace(shape.getId(), subject.serviceShape))
                .toList();
    }

    JavaFile modeledEnum(StringShape stringShape) {
        return ModeledEnum.javaFile(modelPackageName, stringShape);
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
