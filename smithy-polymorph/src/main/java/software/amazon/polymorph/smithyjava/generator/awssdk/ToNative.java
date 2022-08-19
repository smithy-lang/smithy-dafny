package software.amazon.polymorph.smithyjava.generator.awssdk;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.TypeSpec;

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

import javax.lang.model.element.Modifier;

import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ShapeType;
import software.amazon.smithy.model.shapes.StructureShape;

import static software.amazon.smithy.utils.StringUtils.capitalize;

/**
 * ToNative is a helper class for the AwsSdk Shim.<p>
 * It contains methods to convert
 * a subset of an AWS SDK Service's types
 * from Dafny generated Java to native Java.<p>
 * The subset is composed of the:
 * <ul>
 *   <li>All the Service's Operations' inputs
 *   <li>All the fields contained by the above
 * </ul>
 */
@SuppressWarnings("OptionalGetWithoutIsPresent")
public class ToNative extends Generator {
    /** Additional Shapes to generate ToNative converters for. */
    final Set<Shape> additionalShapes;
    /** Static imports to be added to generated code. */
    final Set<MethodReference> additionalStaticImports;
    /** The class name of the AWS SDK's Service's Shim's ToNative class. */
    final ClassName thisClassName;

    public ToNative(AwsSdk awsSdk) {
        super(awsSdk);
        additionalShapes = new HashSet<>();
        additionalStaticImports = new HashSet<>();
        thisClassName = ClassName.get(dafnyNameResolver.packageName(), "ToNative");
    }

    @Override
    public JavaFile javaFile(ShapeId serviceShapeId) {
        JavaFile.Builder builder = JavaFile
                .builder(dafnyNameResolver.packageName(), toNative(serviceShapeId));
        additionalStaticImports.forEach(methodReference ->
                builder.addStaticImport(methodReference.className(), methodReference.methodName()));
        return builder.build();
    }

    TypeSpec toNative(final ShapeId serviceShapeId) {
        final ServiceShape serviceShape = model.expectShape(serviceShapeId, ServiceShape.class);

        final List<MethodSpec> convertOperationInputs = serviceShape
                .members()
                .stream()
                .filter(MemberShape::isOperationShape)
                .map(MemberShape::asOperationShape)
                .map(Optional::get)
                .map(OperationShape::getInputShape)
                .map(this::generateConvertStructure)
                .toList();

        final List<MethodSpec> convertAdditional = additionalShapes
                .stream()
                .map(Shape::toShapeId)
                .map(this::generateConvert)
                .filter(Optional::isPresent)
                .map(Optional::get)
                .toList();

        return TypeSpec
                .classBuilder(
                        ClassName.get(dafnyNameResolver.packageName(), "ToNative"))
                .addModifiers(Modifier.PUBLIC)
                .addMethods(convertOperationInputs)
                .addMethods(convertAdditional)
                .build();
    }

    private Optional<MethodSpec> generateConvert(ShapeId shapeId) {
        throw new UnsupportedOperationException("TODO");
    }

    private MethodSpec generateConvertStructure(ShapeId shapeId) {
        final StructureShape structureShape = model.expectShape(shapeId, StructureShape.class);
        String methodName = capitalize(shapeId.getName());
        ClassName nativeClassName = nativeNameResolver.typeForStructure(structureShape);
        MethodSpec.Builder builder = MethodSpec
                .methodBuilder(methodName)
                .addModifiers(Modifier.STATIC, Modifier.PUBLIC)
                .returns(nativeClassName)
                .addParameter(dafnyNameResolver.typeForShape(shapeId), "dafnyValue");

        if (structureShape.members().size() == 0) {
            builder.addStatement("return new $T()", dafnyNameResolver.typeForShape(shapeId));
            return builder.build();
        }
        builder.addStatement("$T converted = new $T()", nativeClassName, nativeClassName);

        // For each member
        // // if not optional, set with conversion call, get via Field
        structureShape.members().stream().filter(MemberShape::isRequired)
                .forEach(requiredMember ->
                        builder.addStatement(setWithConversionCall(requiredMember)));

        // // if optional
        // // // if present, set with conversion call, get via dtor_values()
        structureShape.members().stream().filter(MemberShape::isOptional)
                .forEach(optionalMember -> {
                    builder.beginControlFlow("if (dafnyValue.$L.is_Some()");
                    builder.addStatement(setWithConversionCall(optionalMember));
                    builder.endControlFlow();
                });
        return builder.addStatement("return converted").build();
    }

    private CodeBlock setWithConversionCall(MemberShape member) {
        return CodeBlock.of("converted.$L($L($L))",
                setMemberField(member),
                memberConversionMethodReference(member).asNormalReference(),
                getMemberField(member));
    }

    private CodeBlock getMemberField(MemberShape requiredMember) {
        // if required, get via Field
        // if optional, get via dtor_values()
        throw new UnsupportedOperationException("TODO");
    }

    private MethodReference memberConversionMethodReference(MemberShape requiredMember) {
        throw new UnsupportedOperationException("TODO");
    }

    private CodeBlock setMemberField(MemberShape requiredMember) {
        throw new UnsupportedOperationException("TODO");
    }

    private MethodSpec generateConvertEnum(ShapeId shapeId) {
        throw new UnsupportedOperationException("TODO");
    }

    /**
     * The keys are the Dafny generated java input type,
     * the values are the method that converts
     * from that input to the idiomatic java type.
     */
    static final Map<ShapeType, MethodReference> AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE;
    static final Map<ShapeType, MethodReference> SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE;
    static final ClassName COMMON_TO_NATIVE_SIMPLE = ClassName.get(software.amazon.dafny.conversion.ToNative.Simple.class);
    static final ClassName COMMON_TO_NATIVE_AGGREGATE = ClassName.get(software.amazon.dafny.conversion.ToNative.Aggregate.class);

    static {
        AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE = Map.ofEntries(
                Map.entry(ShapeType.LIST, new MethodReference(COMMON_TO_NATIVE_AGGREGATE, "GenericToList")),
                Map.entry(ShapeType.SET, new MethodReference(COMMON_TO_NATIVE_AGGREGATE,"GenericToSet")),
                Map.entry(ShapeType.MAP, new MethodReference(COMMON_TO_NATIVE_AGGREGATE,"GenericToMap"))
        );
        SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE = Map.ofEntries(
                Map.entry(ShapeType.BLOB, new MethodReference(COMMON_TO_NATIVE_SIMPLE, "ByteBuffer")),
                Map.entry(ShapeType.BOOLEAN, Constants.IDENTITY_FUNCTION),
                Map.entry(ShapeType.STRING, new MethodReference(COMMON_TO_NATIVE_SIMPLE, "String")),
                // TODO: Timestamp should be service specific
                Map.entry(ShapeType.TIMESTAMP, new MethodReference(COMMON_TO_NATIVE_SIMPLE, "Date")),
                Map.entry(ShapeType.BYTE, Constants.IDENTITY_FUNCTION),
                Map.entry(ShapeType.SHORT, Constants.IDENTITY_FUNCTION),
                Map.entry(ShapeType.INTEGER, Constants.IDENTITY_FUNCTION),
                Map.entry(ShapeType.LONG, Constants.IDENTITY_FUNCTION),
                Map.entry(ShapeType.BIG_DECIMAL, Constants.IDENTITY_FUNCTION),
                Map.entry(ShapeType.BIG_INTEGER, Constants.IDENTITY_FUNCTION)
        );
    }
}
