package software.amazon.polymorph.smithyjava.generator.awssdk;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.ParameterSpec;
import com.squareup.javapoet.TypeSpec;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import javax.lang.model.element.Modifier;

import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.shapes.ListShape;
import software.amazon.smithy.model.shapes.MapShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.SetShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ShapeType;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.EnumDefinition;
import software.amazon.smithy.model.traits.EnumTrait;

import static software.amazon.polymorph.smithyjava.generator.awssdk.Generator.Constants.IDENTITY_FUNCTION;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.SMITHY_API_UNIT;
import static software.amazon.smithy.utils.StringUtils.capitalize;
import static software.amazon.smithy.utils.StringUtils.uncapitalize;

/**
 * ToNative is a helper class for the AwsSdk's {@link Shim}.<p>
 * It contains methods to convert
 * a subset of an AWS SDK Service's types
 * from Dafny generated Java to native Java.<p>
 * The subset is composed of the:
 * <ul>
 *   <li>All the Service's Operations' inputs
 *   <li>All the fields contained by the above
 * </ul>
 */
public class ToNative extends Generator {
    /**
     * The keys are the Dafny generated java input type,
     * the values are the method that converts from that input to
     * the idiomatic java type.
     */
    static final Map<ShapeType, MethodReference> AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE;
    static final Map<ShapeType, MethodReference> SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE;
    static final ClassName COMMON_TO_NATIVE_SIMPLE = ClassName.get(software.amazon.dafny.conversion.ToNative.Simple.class);
    static final ClassName COMMON_TO_NATIVE_AGGREGATE = ClassName.get(software.amazon.dafny.conversion.ToNative.Aggregate.class);
    private final static String VAR_INPUT = "dafnyValue";
    private final static String VAR_OUTPUT = "converted";
    private final static String VAR_TEMP = "temp";
    private final static String TO_NATIVE = "ToNative";
    private static final Logger LOGGER = LoggerFactory.getLogger(ToNative.class);

    static {
        AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE = Map.ofEntries(
                Map.entry(ShapeType.LIST, new MethodReference(COMMON_TO_NATIVE_AGGREGATE, "GenericToList")),
                Map.entry(ShapeType.SET, new MethodReference(COMMON_TO_NATIVE_AGGREGATE, "GenericToSet")),
                Map.entry(ShapeType.MAP, new MethodReference(COMMON_TO_NATIVE_AGGREGATE, "GenericToMap"))
        );
        SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE = Map.ofEntries(
                Map.entry(ShapeType.BLOB, new MethodReference(COMMON_TO_NATIVE_SIMPLE, "ByteBuffer")),
                Map.entry(ShapeType.BOOLEAN, IDENTITY_FUNCTION),
                Map.entry(ShapeType.STRING, new MethodReference(COMMON_TO_NATIVE_SIMPLE, "String")),
                // TODO: Timestamp should be service specific
                Map.entry(ShapeType.TIMESTAMP, new MethodReference(COMMON_TO_NATIVE_SIMPLE, "Date")),
                Map.entry(ShapeType.BYTE, IDENTITY_FUNCTION),
                Map.entry(ShapeType.SHORT, IDENTITY_FUNCTION),
                Map.entry(ShapeType.INTEGER, IDENTITY_FUNCTION),
                Map.entry(ShapeType.LONG, IDENTITY_FUNCTION),
                Map.entry(ShapeType.BIG_DECIMAL, IDENTITY_FUNCTION),
                Map.entry(ShapeType.BIG_INTEGER, IDENTITY_FUNCTION)
        );
    }

    /** The class name of the AWS SDK's Service's Shim's ToNative class. */
    final ClassName thisClassName;

    public ToNative(AwsSdk awsSdk) {
        super(awsSdk);
        thisClassName = ClassName.get(dafnyNameResolver.packageName(), TO_NATIVE);
    }

    @Override
    public JavaFile javaFile(ShapeId serviceShapeId) {
        JavaFile.Builder builder = JavaFile
                .builder(dafnyNameResolver.packageName(), toNative(serviceShapeId));
        return builder.build();
    }

    @SuppressWarnings("DuplicatedCode")
    TypeSpec toNative(final ShapeId serviceShapeId) {
        final ServiceShape serviceShape = model.expectShape(serviceShapeId, ServiceShape.class);
        LinkedHashSet<ShapeId> operationInputs = serviceShape.getOperations().stream()
                .map(shapeId -> model.expectShape(shapeId, OperationShape.class))
                .map(OperationShape::getInputShape)
                .collect(Collectors.toCollection(LinkedHashSet::new));
        Set<ShapeId> allRelevantShapeIds = ModelUtils.findAllDependentShapes(operationInputs, model);
        List<MethodSpec> convertRelevant = allRelevantShapeIds.stream()
                .map(this::generateConvert).filter(Objects::nonNull).toList();
        return TypeSpec
                .classBuilder(
                        ClassName.get(dafnyNameResolver.packageName(), TO_NATIVE))
                .addModifiers(Modifier.PUBLIC)
                .addMethods(convertRelevant)
                .build();
    }

    @SuppressWarnings({"OptionalGetWithoutIsPresent", "DuplicatedCode"})
    MethodSpec generateConvert(ShapeId shapeId) {
        final Shape shape = model.getShape(shapeId)
                .orElseThrow(() -> new IllegalStateException("Cannot find shape " + shapeId));
        return switch (shape.getType()) {
            // For the AWS SDK for Java V1, we do not generate converters for simple shapes
            case BLOB, BOOLEAN, INTEGER, LONG, TIMESTAMP, MEMBER -> null;
            case STRING -> generateConvertString(shapeId); // STRING handles enums
            case LIST -> generateConvertList(shape.asListShape().get());
            case MAP -> generateConvertMap(shape.asMapShape().get());
            case SET -> generateConvertSet(shape.asSetShape().get());
            case STRUCTURE -> generateConvertStructure(shapeId);
            default -> throw new UnsupportedOperationException(
                    "ShapeId %s is of Type %s, which is not yet supported for ToDafny"
                            .formatted(shapeId, shape.getType()));
        };
    }

    MethodSpec generateConvertSet(SetShape shape) {
        MemberShape memberShape = shape.getMember();
        CodeBlock memberConverter = memberConversionMethodReference(memberShape).asFunctionalReference();
        CodeBlock genericCall = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(shape.getType()).asNormalReference();
        ParameterSpec parameterSpec = ParameterSpec
                .builder(dafnyNameResolver.typeForShape(shape.getId()), VAR_INPUT)
                .build();
        return MethodSpec
                .methodBuilder(capitalize(shape.getId().getName()))
                .addModifiers(Modifier.PUBLIC, Modifier.STATIC)
                .returns(nativeNameResolver.typeForShape(shape.getId()))
                .addParameter(parameterSpec)
                .addStatement("return $L($L, $L)",
                        genericCall, VAR_INPUT, memberConverter)
                .build();
    }

    @SuppressWarnings("OptionalGetWithoutIsPresent")
    MethodSpec generateConvertMap(MapShape shape) {
        MemberShape keyShape = shape.getKey().asMemberShape().get();
        CodeBlock keyConverter = memberConversionMethodReference(keyShape).asFunctionalReference();
        MemberShape valueShape = shape.getValue().asMemberShape().get();
        CodeBlock valueConverter = memberConversionMethodReference(valueShape).asFunctionalReference();
        CodeBlock genericCall = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(shape.getType()).asNormalReference();
        ParameterSpec parameterSpec = ParameterSpec
                .builder(dafnyNameResolver.typeForShape(shape.getId()), VAR_INPUT)
                .build();
        return MethodSpec
                .methodBuilder(capitalize(shape.getId().getName()))
                .addModifiers(Modifier.PUBLIC, Modifier.STATIC)
                .returns(nativeNameResolver.typeForShape(shape.getId()))
                .addParameter(parameterSpec)
                .addStatement("return $L($L, $L, $L)",
                        genericCall, VAR_INPUT, keyConverter, valueConverter)
                .build();
    }

    MethodSpec generateConvertList(ListShape shape) {
        MemberShape memberShape = shape.getMember();
        CodeBlock memberConverter = memberConversionMethodReference(memberShape).asFunctionalReference();
        CodeBlock genericCall = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(shape.getType()).asNormalReference();
        ParameterSpec parameterSpec = ParameterSpec
                .builder(dafnyNameResolver.typeForShape(shape.getId()), VAR_INPUT)
                .build();
        return MethodSpec
                .methodBuilder(capitalize(shape.getId().getName()))
                .addModifiers(Modifier.PUBLIC, Modifier.STATIC)
                .returns(nativeNameResolver.typeForShape(shape.getId()))
                .addParameter(parameterSpec)
                .addStatement("return $L(\n$L, \n$L)",
                        genericCall, VAR_INPUT, memberConverter)
                .build();

    }

    MethodSpec generateConvertStructure(ShapeId shapeId) {
        if (shapeId.equals(SMITHY_API_UNIT)) {
            // TODO: handle no input
            LOGGER.error("This Operation takes `smithy.api#Unit, which is currently unsupported: %s".formatted(shapeId));
            return null;
        }
        final StructureShape structureShape = model.expectShape(shapeId, StructureShape.class);
        String methodName = capitalize(shapeId.getName());
        ClassName nativeClassName = nativeNameResolver.typeForStructure(structureShape);
        MethodSpec.Builder builder = MethodSpec
                .methodBuilder(methodName)
                .addModifiers(Modifier.STATIC, Modifier.PUBLIC)
                .returns(nativeClassName)
                .addParameter(dafnyNameResolver.typeForShape(shapeId), VAR_INPUT);

        if (structureShape.members().size() == 0) {
            builder.addStatement("return new $T()", nativeClassName);
            return builder.build();
        }
        builder.addStatement("$T $L = new $T()", nativeClassName, VAR_OUTPUT, nativeClassName);

        // For each member
        structureShape.members()
                .forEach(member -> {
                    // if optional, check if present
                    if (member.isOptional()) {
                        builder.beginControlFlow("if ($L.$L.is_Some())", VAR_INPUT, getMemberField(member));
                    }
                    // if converting a LIST or SET of enums
                    if (nativeNameResolver.isListOrSetOfEnums(member.getTarget())) {
                        // create temp array
                        builder.addStatement(initTempArray(member));
                        // set with conversion call and toArray
                        builder.addStatement(setWithConversionCallAndToArray(member));
                    } else {
                        // set with conversion call
                        builder.addStatement(setWithConversionCall(member));
                    }
                    if (member.isOptional()) builder.endControlFlow();
                });
        return builder.addStatement("return $L", VAR_OUTPUT).build();
    }

    CodeBlock getMemberField(MemberShape shape) {
        return CodeBlock.of("$L", capitalize(shape.getMemberName()));
    }

    CodeBlock getMemberFieldValue(MemberShape shape) {
        // if required, get via Field
        if (shape.isRequired()) {
            return getMemberField(shape);
        }
        // if optional, get via dtor_value()
        return CodeBlock.of("$L.dtor_value()", getMemberField(shape));
    }

    /**
     * Generates an Array of member's type with size of input's field.
     * i.e:<p> {@code MemberType[] member_temp = new MemberType[dafnyValue.Member.length()];}
     */
    CodeBlock initTempArray(MemberShape member) {
        return CodeBlock.of("$T[] $L_$L = new $T[$L.$L.$L]",
                nativeNameResolver.typeForListOrSetMember(member.getTarget()),
                uncapitalize(member.getMemberName()), VAR_TEMP,
                nativeNameResolver.typeForListOrSetMember(member.getTarget()),
                VAR_INPUT, getMemberFieldValue(member),
                Dafny.aggregateSizeMethod(model.expectShape(member.getTarget()).getType()));
    }

    CodeBlock setWithConversionCall(MemberShape member) {
        return CodeBlock.of("$L.$L($L($L.$L))",
                VAR_OUTPUT,
                setMemberField(member),
                memberConversionMethodReference(member).asNormalReference(),
                VAR_INPUT,
                getMemberFieldValue(member));
    }

    CodeBlock setWithConversionCallAndToArray(MemberShape member) {
        return CodeBlock.of("$L.$L($L($L.$L).toArray($L_$L))",
                VAR_OUTPUT,
                setMemberField(member),
                memberConversionMethodReference(member).asNormalReference(),
                VAR_INPUT,
                getMemberFieldValue(member),
                uncapitalize(member.getMemberName()), VAR_TEMP);
    }

    CodeBlock setMemberField(MemberShape shape) {
        // In AWS SDK Java v1, using `with` allows for enums or strings
        // while `set` only allows for strings.
        return CodeBlock.of("with$L", capitalize(shape.getMemberName()));
    }

    /**
     * Returns MethodReference that converts from
     * the Java Dafny memberShape to
     * the Java Native memberShape.
     */
    @SuppressWarnings({"DuplicatedCode", "OptionalGetWithoutIsPresent"})
    MethodReference memberConversionMethodReference(MemberShape memberShape) {
        Shape target = model.getShape(memberShape.getTarget()).get();
        // If the target is simple, use SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE
        if (ModelUtils.isSmithyApiOrSimpleShape(target)) {
            return SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(target.getType());
        }
        final String methodName = capitalize(target.getId().getName());
        // if in namespace reference created converter
        if (nativeNameResolver.isInServiceNameSpace(target.getId())) {
            return new MethodReference(thisClassName, methodName);
        }
        // Otherwise, this target must be in another namespace
        ClassName otherNamespaceToDafny = ClassName.get(
                Dafny.packageNameForNamespace(target.getId().getNamespace()),
                TO_NATIVE
        );
        return new MethodReference(otherNamespaceToDafny, methodName);
    }

    MethodSpec generateConvertString(ShapeId shapeId) {
        final StringShape shape = model.expectShape(shapeId, StringShape.class);
        if (shape.hasTrait(EnumTrait.class)) {
            return generateConvertEnum(shapeId);
        }
        return null;
    }

    @SuppressWarnings("OptionalGetWithoutIsPresent")
    MethodSpec generateConvertEnum(ShapeId shapeId) {
        final StringShape shape = model.expectShape(shapeId, StringShape.class);
        String methodName = capitalize(shapeId.getName());
        final EnumTrait enumTrait = shape.getTrait(EnumTrait.class).orElseThrow();
        if (!enumTrait.hasNames()) {
            throw new UnsupportedOperationException("Unnamed enums not supported");
        }
        ClassName nativeEnumClass = nativeNameResolver.classForEnum(shape);

        MethodSpec.Builder builder = MethodSpec
                .methodBuilder(methodName)
                .addModifiers(Modifier.STATIC, Modifier.PUBLIC)
                .returns(nativeEnumClass)
                .addParameter(dafnyNameResolver.classForShape(shape), VAR_INPUT);

        enumTrait.getValues().stream()
                .map(EnumDefinition::getName)
                .map(Optional::get)
                .peek(name -> {
                    if (!ModelUtils.isValidEnumDefinitionName(name)) {
                        throw new UnsupportedOperationException(
                                "Invalid enum definition name: %s".formatted(name));
                    }
                })
                .forEach(name -> builder
                        .beginControlFlow("if ($L.$L())", VAR_INPUT, Dafny.enumIsName(name))
                        .addStatement("return $T.$L", nativeEnumClass, name)
                        .endControlFlow()
                );

        builder.addStatement("return $T.fromValue($L.toString())", nativeEnumClass, VAR_INPUT);
        return builder.build();
    }
}
