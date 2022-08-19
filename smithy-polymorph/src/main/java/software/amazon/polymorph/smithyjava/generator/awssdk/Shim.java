package software.amazon.polymorph.smithyjava.generator.awssdk;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.ParameterizedTypeName;
import com.squareup.javapoet.TypeName;
import com.squareup.javapoet.TypeSpec;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.Optional;
import java.util.stream.Collectors;

import javax.lang.model.element.Modifier;

import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.utils.StringUtils;


/**
 * Generates an AWS SDK Shim
 * exposing an AWS Service's operations to Dafny Generated Java.
 */
public class Shim extends Generator {
    private static final Logger LOGGER = LoggerFactory.getLogger(Shim.class);

    public Shim(ServiceShape serviceShape, Model model) {
        super(serviceShape, model);
    }

    public Shim(AwsSdk awsSdk) {
        super(awsSdk);
    }

    @Override
    public JavaFile javaFile(final ShapeId serviceShapeId) {
        return JavaFile.builder(dafnyNameResolver.packageName(), shim(serviceShapeId))
                .build();
    }

    TypeSpec shim(final ShapeId serviceShapeId) {
        final ServiceShape serviceShape = model.expectShape(serviceShapeId, ServiceShape.class);
        return TypeSpec
                .classBuilder(
                        ClassName.get(dafnyNameResolver.packageName(), "Shim"))
                .addModifiers(Modifier.PUBLIC)
                .addSuperinterface(dafnyNameResolver.typeForShape(serviceShapeId))
                .addField(
                        nativeNameResolver.typeForService(serviceShape),
                        "_impl", Modifier.PRIVATE, Modifier.FINAL)
                .addMethod(constructor())
                .addMethods(
                        serviceShape.getAllOperations()
                                .stream()
                                .map(this::operation)
                                .filter(Optional::isPresent)
                                .map(Optional::get)
                                .collect(Collectors.toList()))
                .build();
    }

    MethodSpec constructor() {
        return MethodSpec
                .constructorBuilder()
                .addModifiers(Modifier.PUBLIC)
                .addParameter(
                        nativeNameResolver.typeForService(serviceShape),
                        "impl")
                .addStatement("_impl = impl")
                .build();
    }

    Optional<MethodSpec> operation(final ShapeId operationShapeId) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);
        if (operationShape.getOutput().isEmpty()) {
            // TODO: handle empty returns via dafny tuple_0
            LOGGER.error("This Operation returns `smithy.api#Unit, which is currently unsupported: %s".formatted(operationShapeId));
            return Optional.empty();
        }
        ShapeId inputShapeId = operationShape.getInputShape();
        ShapeId outputShapeId = operationShape.getOutputShape();
        TypeName dafnyOutput = dafnyNameResolver.typeForShape(outputShapeId);
        String operationName = operationShape.toShapeId().getName();
        MethodSpec.Builder builder = MethodSpec
                .methodBuilder(StringUtils.capitalize(operationName))
                .addAnnotation(Override.class)
                .addModifiers(Modifier.PUBLIC)
                .returns(
                        asDafnyResult(
                                dafnyOutput,
                                dafnyNameResolver.getDafnyAbstractServiceError()
                        ))
                .addParameter(dafnyNameResolver.typeForShape(inputShapeId), "input")
                .addStatement("$T converted = ToNative.$L(input)",
                        nativeNameResolver.typeForShape(inputShapeId),
                        StringUtils.capitalize(inputShapeId.getName()))
                .beginControlFlow("try")
                // TODO: This assumes the operation has an output
                .addStatement("$T result = _impl.$L(converted)",
                        nativeNameResolver.typeForOperationOutput(outputShapeId),
                        StringUtils.uncapitalize(operationName))
                .addStatement("$T dafnyResponse = ToDafny.$L(result)",
                        dafnyOutput,
                        StringUtils.capitalize(outputShapeId.getName()))
                .addStatement("return Result.create_Success(dafnyResponse)");

        operationShape.getErrors().forEach(shapeId ->
                builder
                        .nextControlFlow("catch ($T ex)", nativeNameResolver.typeForShape(shapeId))
                        .addStatement("return Result.create_Failure(ToDafny.Error(ex))")
        );
        return Optional.of(builder
                .nextControlFlow("catch ($T ex)", nativeNameResolver.baseErrorForService())
                .addStatement("return Result.create_Failure(ToDafny.Error(ex))")
                .endControlFlow()
                .build());
    }

    private TypeName asDafnyResult(TypeName success, TypeName failure) {
        return ParameterizedTypeName.get(
                ClassName.get("Wrappers_Compile", "Result"),
                success,
                failure
        );
    }
}
