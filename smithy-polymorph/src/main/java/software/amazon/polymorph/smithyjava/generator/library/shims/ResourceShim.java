package software.amazon.polymorph.smithyjava.generator.library.shims;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.FieldSpec;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeSpec;

import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.polymorph.smithyjava.generator.library.ShimLibrary;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;

import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ResourceShape;

import static javax.lang.model.element.Modifier.ABSTRACT;
import static javax.lang.model.element.Modifier.FINAL;
import static javax.lang.model.element.Modifier.PROTECTED;
import static javax.lang.model.element.Modifier.PUBLIC;


public class ResourceShim extends ShimLibrary {
    /** The Resource Shape the Shim wraps. */
    protected final ResourceShape targetShape;
    protected final ClassName interfaceName;
    /** The class name of the Subject's Shim class. */
    protected final ClassName thisClassName;


    public ResourceShim(JavaLibrary javaLibrary, ResourceShape targetShape) {
        super(javaLibrary);
        this.targetShape = targetShape;
        /*this.thisClassName = ClassName.get(javaLibrary.packageName, targetShape.toShapeId().getName());*/
        this.thisClassName = subject.nativeNameResolver.classNameForResource(targetShape);
        this.interfaceName = subject.nativeNameResolver.classNameForInterfaceOrLocalService(targetShape);
    }

    @Override
    public Set<JavaFile> javaFiles() {
        JavaFile.Builder shimFile = JavaFile
                .builder(thisClassName.packageName(), shim());
        JavaFile.Builder interfaceFile = JavaFile
                .builder(thisClassName.packageName(), resourceInterface());
        /*return Set.of(interfaceFile.build());*/
        return Set.of(interfaceFile.build(), shimFile.build());
    }

    TypeSpec shim() {
        TypeSpec.Builder spec = TypeSpec
                .classBuilder(thisClassName)
                .addModifiers(PUBLIC)
                .addField(getField())
                .addMethod(resourceConstructor())
                .addMethod(impl())
                .addSuperinterface(interfaceName);
        spec.addMethods(getOperationsForTarget()
                .stream().sequential().map(this::operation).collect(Collectors.toList()));
        return spec.build();
    }

    TypeSpec resourceInterface() {
        TypeSpec.Builder spec = TypeSpec
                .interfaceBuilder(interfaceName)
                .addModifiers(PUBLIC);
        spec.addMethods(getOperationsForTarget()
                .stream().sequential().map(this::operationMethodSignature)
                .map(JavaLibrary.MethodSignature::method)
                .map(method -> method.addModifiers(PUBLIC, ABSTRACT))
                .map(MethodSpec.Builder::build)
                .collect(Collectors.toList()));
        spec.addMethod(implMethodSignature().addModifiers(PUBLIC, ABSTRACT).build());
        return spec.build();
    }

    protected MethodSpec impl() {
        return implMethodSignature()
                .addModifiers(PUBLIC)
                .addStatement("return this.$L", DAFNY_INTERFACE_FIELD)
                .build();
    }

    protected MethodSpec.Builder implMethodSignature() {
        return MethodSpec.methodBuilder("impl")
                .returns(Dafny.interfaceForResource(targetShape));
    }

    private MethodSpec resourceConstructor() {
        return MethodSpec.constructorBuilder()
                .addModifiers(PROTECTED)
                .addParameter(Dafny.interfaceForResource(targetShape), DAFNY_INTERFACE_FIELD, FINAL)
                .addStatement("this.$L = $L", DAFNY_INTERFACE_FIELD, DAFNY_INTERFACE_FIELD)
                .build();
    }

    protected FieldSpec getField() {
        return FieldSpec
                .builder(Dafny.interfaceForResource(targetShape), DAFNY_INTERFACE_FIELD)
                .addModifiers(PRIVATE_FINAL)
                .build();
    }

    protected List<OperationShape> getOperationsForTarget() {
        return targetShape.getOperations().stream().sequential()
                .map(shapeId -> subject.model.expectShape(shapeId, OperationShape.class))
                .collect(Collectors.toList());
    }
}
