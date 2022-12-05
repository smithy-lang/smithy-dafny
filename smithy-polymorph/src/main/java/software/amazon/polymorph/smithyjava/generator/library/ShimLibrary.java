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
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.Shape;
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
    /** The Service or Resource Shape the Shim wraps. */
    protected final Shape targetShape;

    public ShimLibrary(JavaLibrary javaLibrary, Shape targetShape) {
        super(javaLibrary);
        this.subject = javaLibrary;
        if (!(targetShape.isResourceShape() || targetShape.isServiceShape())) {
            throw new IllegalArgumentException(
                    "targetShape MUST be a Resource or Service Shape. ShapeId: %s".formatted(targetShape.toShapeId()));
        }
        if (!targetShape.isServiceShape()) {
            // TODO: Handle Resources
            throw new IllegalArgumentException(
                    "targetShape MUST be a Service Shape with LocalTrait. ShapeId: %s".formatted(targetShape.toShapeId()));
        }
        //noinspection OptionalGetWithoutIsPresent
        this.targetShape = targetShape.asServiceShape().get();
        LocalServiceTrait trait = targetShape.expectTrait(LocalServiceTrait.class);
        this.thisClassName = ClassName.get(javaLibrary.packageName, trait.getSdkId());
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
                        // TODO: Handle Resources (serviceBuilderImplBuildMethod assumes this is a service)
                        serviceBuilderImplBuildMethod()
                ))
                // TODO: Handle Resources (serviceConstructor assumes this is a service)
                .addMethod(serviceConstructor(builderSpecs))
                .addMethod(builderSpecs.builderMethod());
        spec.addMethods(getOperationsForTarget()
                .stream().sequential().map(this::operation).collect(Collectors.toList()));
        return spec.build();
    }

    public List<OperationShape> getOperationsForTarget() {
        if (!targetShape.isServiceShape()) {
            // TODO: Handle Resources
            throw new IllegalArgumentException(
                    "targetShape MUST be a Service Shape with LocalTrait. ShapeId: %s".formatted(targetShape.toShapeId()));
        }
        //noinspection OptionalGetWithoutIsPresent
        return targetShape.asServiceShape().get().getOperations().stream().sequential()
                .map(shapeId -> subject.model.expectShape(shapeId, OperationShape.class))
                .collect(Collectors.toList());
    }

    private MethodSpec operation(OperationShape operationShape) {
        final ShapeId inputShapeId = operationShape.getInputShape();
        ShapeId inputTargetId = inputShapeId;
        final ShapeId outputShapeId = operationShape.getOutputShape();
        ShapeId outputTargetId = outputShapeId;
        final String operationName = operationShape.toShapeId().getName();
        final MethodSpec.Builder method = MethodSpec
                .methodBuilder(operationName)
                .addModifiers(PUBLIC);
        // if operation takes an argument
        if (!inputShapeId.equals(SMITHY_API_UNIT)) {
            // Positional complicates everything, see dafnyDeclareAndConvert
            inputTargetId = subject.checkForPositional(inputShapeId);
            TypeName inputType = subject.nativeNameResolver.typeForShape(inputTargetId);
            // Add parameter to method signature
            method.addParameter(inputType, NATIVE_VAR);
            // if inputValue has ReferenceTrait.trait
            if (subject.model.expectShape(inputTargetId).hasTrait(ReferenceTrait.class)) {
                // do NOT convert, just declare as dafnyValue
                method.addStatement(dafnyDeclare(inputTargetId));
            } else {
                // Convert from nativeValue to dafnyValue
                method.addStatement(dafnyDeclareAndConvert(inputTargetId, inputShapeId));
            }
        }
        // A void result in Dafny Java is Tuple0
        TypeName success = DAFNY_TUPLE0_CLASS_NAME;
        // if operation is not void
        if (!outputShapeId.equals(SMITHY_API_UNIT)) {
            outputTargetId = subject.checkForPositional(outputShapeId);
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
        // if outputShape is Reference
        if (subject.model.expectShape(outputTargetId).hasTrait(ReferenceTrait.class)) {
            // do NOT convert, just return success and return
            method.addStatement("return $L.dtor_value()", RESULT_VAR);
            return method.build();
        }
        // else convert success to native and return
        method.addStatement("return $T.$L($L.dtor_value())",
                toNativeClassName, outputShapeId.getName(), RESULT_VAR);
        return method.build();
    }

    private FieldSpec getArg() {
        if (!targetShape.isServiceShape()) {
            // TODO: Handle Resources
            throw new IllegalArgumentException(
                    "targetShape MUST be a Service Shape with LocalTrait. ShapeId: %s".formatted(targetShape.toShapeId()));
        }
        LocalServiceTrait trait = targetShape.expectTrait(LocalServiceTrait.class);
        return FieldSpec.builder(
                subject.nativeNameResolver.typeForShape(trait.getConfigId()),
                trait.getConfigId().getName()).build();
    }

    private FieldSpec getField() {
        if (!targetShape.isServiceShape()) {
            // TODO: Handle Resources
            throw new IllegalArgumentException(
                    "targetShape MUST be a Service Shape with LocalTrait. ShapeId: %s".formatted(targetShape.toShapeId()));
        }
        return FieldSpec.builder(
                        subject.dafnyNameResolver.typeForShape(
                                targetShape.toShapeId()),
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
    private MethodSpec serviceBuilderImplBuildMethod() {
        if (!targetShape.isServiceShape()) {
            // TODO: Handle Resources
            throw new IllegalArgumentException(
                    "targetShape MUST be a Service Shape with LocalTrait. ShapeId: %s".formatted(targetShape.toShapeId()));
        }
        return MethodSpec.methodBuilder("build")
                .addModifiers(Modifier.PUBLIC)
                .returns(thisClassName)
                // A resource would not need a requiredCheck
                .addCode(BuildMethod.requiredCheck(getArg()))
                .addStatement("return new $T(this)", thisClassName)
                .build();
    }

    private MethodSpec serviceConstructor(BuilderSpecs builderSpecs) {
        if (!targetShape.isServiceShape()) {
            // TODO: Handle Resources
            throw new IllegalArgumentException(
                    "targetShape MUST be a Service Shape with LocalTrait. ShapeId: %s".formatted(targetShape.toShapeId()));
        }
        LocalServiceTrait trait = targetShape.expectTrait(LocalServiceTrait.class);
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
        method.addStatement(dafnyDeclareAndConvert(trait.getConfigId()));
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

    // Reference also adds a complication,
    // as they do not need to be converted.
    private CodeBlock dafnyDeclare(ShapeId targetId) {
        return CodeBlock.of("$T $L = $L",
                subject.dafnyNameResolver.typeForShape(targetId),
                DAFNY_VAR,
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
