package software.amazon.polymorph.smithyjava.generator.library.shims;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeSpec;

import java.util.Set;

import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.polymorph.smithyjava.MethodSignature;
import software.amazon.polymorph.smithyjava.modeled.Operation;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ResourceShape;

import static javax.lang.model.element.Modifier.FINAL;
import static javax.lang.model.element.Modifier.PRIVATE;
import static javax.lang.model.element.Modifier.STATIC;

public class NativeWrapper extends ResourceShim {

    public static ClassName className(ClassName resourceClass) {
        return resourceClass.nestedClass("NativeWrapper");
    }

    public NativeWrapper(JavaLibrary javaLibrary, ResourceShape targetShape) {
        super(javaLibrary, targetShape);
    }

    @Override
    public Set<JavaFile> javaFiles() {
        throw new RuntimeException("NativeWrapper is a nested static class.");
    }

    TypeSpec nativeWrapper() {
        ClassName className = className();
        TypeSpec.Builder spec =TypeSpec
                .classBuilder(className)
                .addModifiers(PRIVATE, FINAL, STATIC)
                .addSuperinterface(Dafny.interfaceForResource(targetShape))
                .addField(interfaceName, INTERFACE_FIELD, PRIVATE, FINAL)
                .addMethod(nativeWrapperConstructor());
        getOperationsForTarget().forEach(oShape -> {
            spec.addMethod(operation(oShape));
            spec.addMethod(operation_K(oShape));
        });
        return spec.build();
    }

    private ClassName className() {
        return className(thisClassName);
    }

    MethodSpec nativeWrapperConstructor() {
        String paramName = "nativeImpl";
        return MethodSpec
                .constructorBuilder()
                .addParameter(interfaceName, paramName)
                .beginControlFlow("if ($L instanceof $T)",
                        paramName, subject.nativeNameResolver.typeForShape(targetShape.getId()))
                .addStatement("throw new $T($S)",
                        IllegalArgumentException.class,
                        "Recursive wrapping is strictly forbidden.")
                .endControlFlow()
                .addStatement("this.$L = $L", INTERFACE_FIELD, paramName)
                .build();
    }

    @Override
    protected MethodSpec operation(OperationShape operationShape) {
        return Operation.AsDafny.operation(operationShape, this.subject, this);
    }

    /**
     *  Polymorph's Smithy-Dafny generates at least two methods for
     *  operations on Resources,
     *  one of which has an {@code `} appended to it.<p>
     *  When this {@code `} suffix is transpiled to Java,
     *  it becomes {@code _k}.<p>
     *  However, this {@code _k} method MUST NOT be implemented natively.<p>
     *  It can only be implemented in Dafny Source,
     *  and then be transpiled.<p>
     *  Hence, we MUST generate this "always throw" method.<p>
     */
    protected MethodSpec operation_K(OperationShape operationShape) {
        final MethodSignature signature = Operation.AsDafny.methodSignature(operationShape, true, subject);
        MethodSpec.Builder method = signature.method();
        method.addStatement("throw $T.builder().message($S).build()",
                subject.nativeNameResolver.baseErrorForService(),
                "Not supported at this time."
                );
        return method.build();
    }
}
