package software.amazon.polymorph.smithyjava.generator.library;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.FieldSpec;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeName;
import com.squareup.javapoet.TypeSpec;

import java.util.Collections;
import java.util.List;
import java.util.Set;
import java.util.stream.Collectors;

import javax.lang.model.element.Modifier;

import software.amazon.polymorph.smithyjava.BuildMethod;
import software.amazon.polymorph.smithyjava.BuilderSpecs;
import software.amazon.polymorph.smithyjava.generator.Generator;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ShapeId;

import static javax.lang.model.element.Modifier.PROTECTED;
import static javax.lang.model.element.Modifier.PUBLIC;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.DAFNY_TUPLE0_CLASS_NAME;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.SMITHY_API_UNIT;


/**
 * A Java Library's Shim is the public class
 * that consumers interact with in Native Java.<p>
 * ShimLibrary holds the logic required to generate the Shim.
 */
public class ShimLibrary extends Generator {
    private static final String INTERFACE_FIELD = "_impl";
    private static final String NATIVE_VAR = "nativeValue";
    private static final String DAFNY_VAR = "dafnyValue";
    private static final String RESULT_VAR = "result";
    // Hack to override CodegenSubject
    // See ModelCodegen for explanation
    final JavaLibrary subject;
    /** The class name of the Subject's Shim class. */
    protected final ClassName thisClassName;
    /** The class name of the Subject's ToDafny class. */
    protected final ClassName toDafnyClassName;
    /** The class name of the Subject's ToNative class. */
    protected final ClassName toNativeClassName;

    public ShimLibrary(JavaLibrary javaLibrary) {
        super(javaLibrary);
        this.subject = javaLibrary;
        this.thisClassName = ClassName.get(
                javaLibrary.packageName, javaLibrary.publicClass);
        this.toDafnyClassName = ToDafnyLibrary.className(javaLibrary);
        this.toNativeClassName = ToNativeLibrary.className(javaLibrary);
    }

    @Override
    public Set<JavaFile> javaFiles() {
        JavaFile.Builder javaFile = JavaFile
                .builder(thisClassName.packageName(), shim());
        return Collections.singleton(javaFile.build());
    }

    TypeSpec shim() {
        List<FieldSpec> shimArgs = List.of(getArg());
        BuilderSpecs builderSpecs = new BuilderSpecs(
                thisClassName, null, shimArgs, Collections.emptyList());
        TypeSpec.Builder spec = TypeSpec
                .classBuilder(thisClassName)
                .addModifiers(Modifier.PUBLIC)
                .addField(getField())
                .addType(builderSpecs.builderInterface())
                .addType(builderSpecs.builderImpl(
                        false,
                        null,
                        builderImplBuildMethod()
                ))
                .addMethod(constructor(builderSpecs))
                .addMethod(builderSpecs.builderMethod());
        spec.addMethods(subject.getOperationsForService()
                .stream().sequential().map(this::operation).collect(Collectors.toList()));
        return spec.build();
    }

    private MethodSpec operation(OperationShape operationShape) {
        ShapeId inputShapeId = operationShape.getInputShape();
        ShapeId outputShapeId = operationShape.getOutputShape();
        String operationName = operationShape.toShapeId().getName();
        MethodSpec.Builder method = MethodSpec
                .methodBuilder(operationName)
                .addModifiers(PUBLIC);
        // if operation takes an argument
        if (!inputShapeId.equals(SMITHY_API_UNIT)) {
            // Positional complicates everything, see dafnyDeclareAndConvert
            ShapeId inputTargetId = subject.checkForPositional(inputShapeId);
            TypeName inputType = subject.nativeNameResolver.typeForShape(inputTargetId);
            // Add parameter to method signature
            method.addParameter(inputType, NATIVE_VAR);
            // Convert from nativeValue to dafnyValue
            method.addStatement(dafnyDeclareAndConvert(inputTargetId, inputShapeId));
        }
        // A void result in Dafny Java is Tuple0
        TypeName success = DAFNY_TUPLE0_CLASS_NAME;
        // if operation is not void
        if (!outputShapeId.equals(SMITHY_API_UNIT)) {
            ShapeId outputTargetId = subject.checkForPositional(outputShapeId);
            TypeName outputType = subject.nativeNameResolver.typeForShape(outputTargetId);
            // Add return type to method signature
            method.returns(outputType);
            // Replace Tuple0 with real type
            success = subject.dafnyNameResolver.typeForShape(outputTargetId);
        }
        TypeName failure = subject.dafnyNameResolver.abstractClassForError();
        //TODO: handle operation specific errors?
        TypeName result = Dafny.asDafnyResult(success, failure);

        // if operation takes an argument
        if (!inputShapeId.equals(SMITHY_API_UNIT)) {
            // call with that argument in dafny
            method.addStatement("$T $L = this.$L.$L($L)",
                    result, RESULT_VAR,
                    INTERFACE_FIELD, operationName, DAFNY_VAR);
        } else {
            // call with no args
            method.addStatement("$T $L = this.$L.$L()",
                    result, RESULT_VAR,
                    INTERFACE_FIELD, operationName);
        }
        // Handle Failure
        method.addCode(ifFailure());

        // if operation is void
        if (outputShapeId.equals(SMITHY_API_UNIT)) {
            return method.build();
        }
        // else convert success to native and return
        method.addStatement("return $T.$L($L.dtor_value())",
                toNativeClassName, outputShapeId.getName(), RESULT_VAR);
        return method.build();
    }

    private FieldSpec getArg() {
        return FieldSpec.builder(
                subject.nativeNameResolver.typeForShape(subject.publicConfigShapeId),
                subject.publicConfigShapeId.getName()).build();
    }

    private FieldSpec getField() {
        return FieldSpec.builder(
                        subject.dafnyNameResolver.typeForShape(
                                subject.serviceShape.toShapeId()),
                        INTERFACE_FIELD)
                .addModifiers(PRIVATE_FINAL)
                .build();
    }

    /*
    The shim is the library's public client.
    A little like the classes in software.amazon.polymorph.smithyjava.unmodeled,
    there are elements of the library's public client
    that are not modeled in a traditional smithy way.
    In particular, we REQUIRE a Config object,
    but there is no @required annotation (or equivalent)
    to inform Smithy that the service client needs a config.
     */
    private MethodSpec builderImplBuildMethod() {
        return MethodSpec.methodBuilder("build")
                .addModifiers(Modifier.PUBLIC)
                .returns(thisClassName)
                .addCode(BuildMethod.requiredCheck(getArg()))
                .addStatement("return new $T(this)", thisClassName)
                .build();
    }

    private MethodSpec constructor(BuilderSpecs builderSpecs) {
        MethodSpec.Builder method =  MethodSpec
                .constructorBuilder()
                .addModifiers(PROTECTED)
                .addParameter(builderSpecs.builderImplName(), BuilderSpecs.BUILDER_VAR);
        // get config from builder
        // i.e: CryptoConfig nativeConfig = builder.CryptoConfig();
        method.addStatement("$T $L = $L.$L()",
                getArg().type,
                NATIVE_VAR,
                BuilderSpecs.BUILDER_VAR,
                getArg().name);
        // convert config to Dafny
        // i.e: Dafny.Aws.Cryptography.Primitives.Types.CryptoConfig dafnyConfig = ToDafny.CryptoConfig(nativeConfig);
        method.addStatement(dafnyDeclareAndConvert(subject.publicConfigShapeId));
        // Invoke client creation
        // i.e.: Result<AtomicPrimitivesClient, Error> result = Dafny.Aws.Cryptography.Primitives.__default.AtomicPrimitives(dafnyValue);
        TypeName success = subject.dafnyNameResolver.classNameForConcreteServiceClient(subject.serviceShape);
        TypeName failure = subject.dafnyNameResolver.abstractClassForError();
        TypeName result = Dafny.asDafnyResult(success, failure);
        method.addStatement("$T $L = $T.$L($L)",
                result, RESULT_VAR,
                subject.dafnyNameResolver.classNameForNamespaceDefault(),
                thisClassName.simpleName(),
                DAFNY_VAR);
        method.addCode(ifFailure());
        method.addStatement("this.$L = $L.dtor_value()", INTERFACE_FIELD, RESULT_VAR);
        return method.build();
    }

    // If it is known the Shape cannot have a positional trait,
    // then the "targetId" and the "shapeId" are the same.
    private CodeBlock dafnyDeclareAndConvert(ShapeId shapeId) {
        return dafnyDeclareAndConvert(shapeId, shapeId);
    }

    // Positional complicates everything.
    // The types need to be looked up by targetId.
    // But The converters are named after the shapeId.
    private CodeBlock dafnyDeclareAndConvert(
            ShapeId targetId, ShapeId shapeId) {
        return CodeBlock.of("$T $L = $T.$L($L)",
                subject.dafnyNameResolver.typeForShape(targetId),
                DAFNY_VAR,
                toDafnyClassName,
                shapeId.getName(),
                NATIVE_VAR);
    }

    private CodeBlock ifFailure() {
        return CodeBlock.builder()
                .beginControlFlow("if ($L.is_Failure())", RESULT_VAR)
                .addStatement("throw $T.Error($L.dtor_error())",
                        toNativeClassName, RESULT_VAR)
                .endControlFlow()
                .build();
    }

}
