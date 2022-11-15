package software.amazon.polymorph.smithyjava.generator.awssdk;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.ParameterSpec;
import com.squareup.javapoet.TypeSpec;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;

import javax.lang.model.element.Modifier;

import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.polymorph.smithyjava.generator.Generator;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.utils.DafnyNameResolverHelpers;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.shapes.ListShape;
import software.amazon.smithy.model.shapes.MapShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.SetShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ShapeType;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.EnumDefinition;
import software.amazon.smithy.model.traits.EnumTrait;

import static software.amazon.polymorph.smithyjava.generator.Generator.Constants.IDENTITY_FUNCTION;
import static software.amazon.smithy.utils.StringUtils.capitalize;
import static software.amazon.smithy.utils.StringUtils.uncapitalize;

/**
 * ToNative is a helper class for the AwsSdk's {@link ShimV1}.<p>
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
    // TODO: for V2 support, use abstract AwsSdk name resolvers and sub class for V1 or V2.
    /** The class name of the AWS SDK's Service's Shim's ToNative class. */
    final ClassName thisClassName;

    public ToNative(JavaAwsSdkV1 awsSdk) {
        super(awsSdk);
        thisClassName = ClassName.get(subject.dafnyNameResolver.packageName(), TO_NATIVE);
    }

    @Override
    public Set<JavaFile> javaFiles() {
        JavaFile.Builder builder = JavaFile
                .builder(subject.dafnyNameResolver.packageName(), toNative());
        return Collections.singleton(builder.build());
    }

    @SuppressWarnings("DuplicatedCode")
    TypeSpec toNative() {
        LinkedHashSet<ShapeId> operationInputs = subject.serviceShape.getOperations().stream()
                .map(shapeId -> subject.model.expectShape(shapeId, OperationShape.class))
                .map(OperationShape::getInputShape)
                .collect(Collectors.toCollection(LinkedHashSet::new));
        Set<ShapeId> allRelevantShapeIds = ModelUtils.findAllDependentShapes(operationInputs, subject.model);
        List<MethodSpec> convertRelevant = allRelevantShapeIds.stream()
                .map(this::generateConvert).filter(Objects::nonNull).toList();
        return TypeSpec
                .classBuilder(
                        ClassName.get(subject.dafnyNameResolver.packageName(), TO_NATIVE))
                .addModifiers(Modifier.PUBLIC)
                .addMethods(convertRelevant)
                .build();
    }

    @SuppressWarnings({"OptionalGetWithoutIsPresent", "DuplicatedCode"})
    MethodSpec generateConvert(ShapeId shapeId) {
        final Shape shape = subject.model.getShape(shapeId)
                .orElseThrow(() -> new IllegalStateException("Cannot find shape " + shapeId));
        return switch (shape.getType()) {
            // For the AWS SDK for Java V1, we do not generate converters for simple shapes
            case BLOB, BOOLEAN, TIMESTAMP, BYTE, SHORT,
                    INTEGER, LONG, BIG_DECIMAL, BIG_INTEGER, MEMBER -> null;
            case STRING -> generateConvertString(shapeId); // STRING handles enums
            case LIST -> generateConvertList(shape.asListShape().get());
            case SET -> generateConvertSet(shape.asSetShape().get());
            case MAP -> generateConvertMap(shape.asMapShape().get());
            case STRUCTURE -> generateConvertStructureV1(shape.asStructureShape().get());
            default -> throw new UnsupportedOperationException(
                    "ShapeId %s is of Type %s, which is not yet supported for ToDafny"
                            .formatted(shapeId, shape.getType()));
        };
    }

    MethodSpec generateConvertSet(SetShape shape) {
        return generateConvertListOrSet(shape.getMember(), shape.getId(), shape.getType());
    }

    MethodSpec generateConvertList(ListShape shape) {
        return generateConvertListOrSet(shape.getMember(), shape.getId(), shape.getType());
    }

    MethodSpec generateConvertListOrSet(MemberShape memberShape, ShapeId shapeId, ShapeType shapeType) {
        CodeBlock memberConverter = memberConversionMethodReference(memberShape).asFunctionalReference();
        CodeBlock genericCall = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(shapeType).asNormalReference();
        ParameterSpec parameterSpec = ParameterSpec
                .builder(subject.dafnyNameResolver.typeForShape(shapeId), VAR_INPUT)
                .build();
        return MethodSpec
                .methodBuilder(capitalize(shapeId.getName()))
                .addModifiers(Modifier.PUBLIC, Modifier.STATIC)
                .returns(subject.nativeNameResolver.typeForShape(shapeId))
                .addParameter(parameterSpec)
                .addStatement("return $L(\n$L, \n$L)",
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
                .builder(subject.dafnyNameResolver.typeForShape(shape.getId()), VAR_INPUT)
                .build();
        return MethodSpec
                .methodBuilder(capitalize(shape.getId().getName()))
                .addModifiers(Modifier.PUBLIC, Modifier.STATIC)
                .returns(subject.nativeNameResolver.typeForShape(shape.getId()))
                .addParameter(parameterSpec)
                .addStatement("return $L(\n$L, \n$L, \n$L)",
                        genericCall, VAR_INPUT, keyConverter, valueConverter)
                .build();
    }

    MethodSpec generateConvertStructureV1(StructureShape structureShape) {
        String methodName = capitalize(structureShape.getId().getName());
        ClassName nativeClassName = subject.nativeNameResolver.typeForStructure(structureShape);
        MethodSpec.Builder builder = MethodSpec
                .methodBuilder(methodName)
                .addModifiers(Modifier.STATIC, Modifier.PUBLIC)
                .returns(nativeClassName)
                .addParameter(subject.dafnyNameResolver.typeForShape(structureShape.getId()), VAR_INPUT);

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
                        builder.beginControlFlow("if ($L.$L.is_Some())", VAR_INPUT, Dafny.getMemberField(member));
                    }
                    // if converting a LIST or SET of enums
                    if (ModelUtils.isListOrSetOfEnums(member.getTarget(), subject.model)) {
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

    /**
     * Generates an Array of member's type with size of input's field.
     * i.e:<p> {@code MemberType[] member_temp = new MemberType[dafnyValue.Member.length()];}
     */
    CodeBlock initTempArray(MemberShape member) {
        return CodeBlock.of("$T[] $L_$L = new $T[$L.$L.$L]",
                subject.nativeNameResolver.typeForListOrSetMember(member.getTarget()),
                uncapitalize(member.getMemberName()), VAR_TEMP,
                subject.nativeNameResolver.typeForListOrSetMember(member.getTarget()),
                VAR_INPUT, Dafny.getMemberFieldValue(member),
                Dafny.aggregateSizeMethod(subject.model.expectShape(member.getTarget()).getType()));
    }

    CodeBlock setWithConversionCall(MemberShape member) {
        return CodeBlock.of("$L.$L($L($L.$L))",
                VAR_OUTPUT,
                setMemberField(member),
                memberConversionMethodReference(member).asNormalReference(),
                VAR_INPUT,
                Dafny.getMemberFieldValue(member));
    }

    CodeBlock setWithConversionCallAndToArray(MemberShape member) {
        return CodeBlock.of("$L.$L($L($L.$L).toArray($L_$L))",
                VAR_OUTPUT,
                setMemberField(member),
                memberConversionMethodReference(member).asNormalReference(),
                VAR_INPUT,
                Dafny.getMemberFieldValue(member),
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
        Shape targetShape = subject.model.getShape(memberShape.getTarget()).get();
        // If the target is simple, use SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE
        if (ModelUtils.isSmithyApiOrSimpleShape(targetShape)) {
            return SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(targetShape.getType());
        }
        final String methodName = capitalize(targetShape.getId().getName());
        // if in namespace reference created converter
        if (subject.nativeNameResolver.isInServiceNameSpace(targetShape.getId())) {
            return new MethodReference(thisClassName, methodName);
        }
        // Otherwise, this target must be in another namespace
        ClassName otherNamespaceToDafny = ClassName.get(
                DafnyNameResolverHelpers.packageNameForNamespace(targetShape.getId().getNamespace()),
                TO_NATIVE
        );
        return new MethodReference(otherNamespaceToDafny, methodName);
    }

    MethodSpec generateConvertString(ShapeId shapeId) {
        final StringShape shape = subject.model.expectShape(shapeId, StringShape.class);
        if (shape.hasTrait(EnumTrait.class)) {
            return generateConvertEnum(shapeId);
        }
        return null;
    }

    @SuppressWarnings("OptionalGetWithoutIsPresent")
    MethodSpec generateConvertEnum(ShapeId shapeId) {
        final StringShape shape = subject.model.expectShape(shapeId, StringShape.class);
        String methodName = capitalize(shapeId.getName());
        final EnumTrait enumTrait = shape.getTrait(EnumTrait.class).orElseThrow();
        if (!enumTrait.hasNames()) {
            throw new UnsupportedOperationException("Unnamed enums not supported");
        }
        ClassName nativeEnumClass = subject.nativeNameResolver.classForEnum(shape);

        MethodSpec.Builder builder = MethodSpec
                .methodBuilder(methodName)
                .addModifiers(Modifier.STATIC, Modifier.PUBLIC)
                .returns(nativeEnumClass)
                .addParameter(subject.dafnyNameResolver.classForShape(shape), VAR_INPUT);

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
                        .beginControlFlow("if ($L.$L())", VAR_INPUT, Dafny.datatypeConstructorIs(name))
                        .addStatement("return $T.$L", nativeEnumClass, name)
                        .endControlFlow()
                );

        builder.addStatement("return $T.fromValue($L.toString())", nativeEnumClass, VAR_INPUT);
        return builder.build();
    }
}
