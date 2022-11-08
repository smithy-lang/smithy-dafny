package software.amazon.polymorph.smithyjava.generator.library;

import com.squareup.javapoet.JavaFile;

import java.util.LinkedHashSet;

import software.amazon.polymorph.smithyjava.generator.Generator;
import software.amazon.polymorph.smithyjava.modeled.ModeledEnum;
import software.amazon.polymorph.smithyjava.modeled.ModeledError;
import software.amazon.polymorph.smithyjava.modeled.ModeledStructure;
import software.amazon.polymorph.smithyjava.unmodeled.CollectionOfErrors;
import software.amazon.polymorph.smithyjava.unmodeled.NativeError;
import software.amazon.polymorph.smithyjava.unmodeled.OpaqueError;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;


class ModelCodegen extends Generator {
    // Hack to override CodegenSubject
    final JavaLibrary subject;
    /** Public Java Interfaces will go here. */
    public final String packageName;
    /** Public POJOs will go here. */
    public final String modelPackageName;

    public ModelCodegen(JavaLibrary subject) {
        super(subject);
        // Hack to override CodegenSubject
        this.subject = subject;
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
        subject.getErrorsInServiceNamespace().stream()
                .map(this::modeledError).forEachOrdered(rtn::add);
        // Structures
        subject.getStructuresInServiceNamespace().stream()
                .map(this::modeledStructure).forEachOrdered(rtn::add);
        // Enums
        subject.getEnumsInServiceNamespace().stream()
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

    JavaFile modeledError(StructureShape shape) {
        return ModeledError.javaFile(modelPackageName, shape, subject);
    }

    JavaFile modeledStructure(StructureShape shape) {
        return ModeledStructure.javaFile(modelPackageName, shape, subject);
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
