package software.amazon.polymorph.smithyjava.generator.awssdk;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.ParameterSpec;
import com.squareup.javapoet.ParameterizedTypeName;
import com.squareup.javapoet.TypeSpec;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

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
import software.amazon.smithy.model.traits.BoxTrait;
import software.amazon.smithy.model.traits.EnumDefinition;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.RequiredTrait;
import software.amazon.smithy.utils.StringUtils;

import static software.amazon.smithy.utils.StringUtils.capitalize;
import static software.amazon.smithy.utils.StringUtils.uncapitalize;

/**
 * ToDafny is a helper class for the AwsSdk Shim.<p>
 * It holds methods to convert
 * a subset of an AWS SDK Service's types to Dafny types.<p>
 * The subset is composed of the:
 * <ul>
 *   <li>All the Service's Operations' outputs
 *   <li>All the Service's Errors
 *   <li>All the fields contained by the above
 * </ul>
 */
@SuppressWarnings("OptionalGetWithoutIsPresent")
public class ToDafny extends Generator {
    /** Additional Shapes to generate ToDafny converters for. */
    final Set<Shape> additionalShapes;
    /** Static imports to be added to generated code. */
    final Set<MethodReference> additionalStaticImports;
    /** Enums need two Methods; a string converter and an Enum converter. */
    final Set<Shape> enumShapes;
    /** The class name of the AWS SDK's Service's Shim's ToDafny class. */
    final ClassName thisClassName;

    public ToDafny(AwsSdk awsSdk) {
        super(awsSdk);
        additionalShapes = new HashSet<>();
        additionalStaticImports = new HashSet<>();
        enumShapes = new HashSet<>();
        thisClassName = ClassName.get(dafnyNameResolver.packageName(), "ToDafny");
    }

    @Override
    public JavaFile javaFile(final ShapeId serviceShapeId) {
        JavaFile.Builder builder = JavaFile
                .builder(dafnyNameResolver.packageName(), toDafny(serviceShapeId));
        additionalStaticImports.forEach(methodReference ->
                builder.addStaticImport(methodReference.className(), methodReference.methodName()));
        return builder.build();
    }

    TypeSpec toDafny(final ShapeId serviceShapeId) {
        final ServiceShape serviceShape = model.expectShape(serviceShapeId, ServiceShape.class);

        final List<MethodSpec> convertOperationOutputs = serviceShape
                .members()
                .stream()
                .filter(MemberShape::isOperationShape)
                .map(MemberShape::asOperationShape)
                .map(Optional::get)
                .map(OperationShape::getOutputShape)
                .map(this::generateConvertResponse)
                .toList();

        final List<MethodSpec> convertServiceErrors = serviceShape
                .getErrors()
                .stream()
                .map(this::generateConvertError)
                .toList();
        convertServiceErrors.add(generateConvertOpaqueError());

        final List<MethodSpec> convertAdditional = additionalShapes
                .stream()
                .map(Shape::toShapeId)
                .map(this::generateConvert)
                .filter(Optional::isPresent)
                .map(Optional::get)
                .toList();
        // For enums, we generate overloaded methods,
        // one to convert instances of the Enum
        final List<MethodSpec> convertEnumEnum = enumShapes
                .stream()
                .map(Shape::toShapeId)
                .map(this::generateConvertEnumEnum)
                .toList();
        // The other to convert String representatives of the enum
        final List<MethodSpec> convertEnumString = enumShapes
                .stream()
                .map(Shape::toShapeId)
                .map(this::generateConvertEnumString)
                .toList();
        return TypeSpec
                .classBuilder(
                        ClassName.get(dafnyNameResolver.packageName(), "ToDafny"))
                .addModifiers(Modifier.PUBLIC)
                .addMethods(convertOperationOutputs)
                .addMethods(convertServiceErrors)
                .addMethods(convertAdditional)
                .addMethods(convertEnumEnum)
                .addMethods(convertEnumString)
                .build();
    }

    MethodSpec generateConvertEnumString(ShapeId shapeId) {
        final StringShape shape = model.expectShape(shapeId, StringShape.class);
        String methodName = capitalize(shapeId.getName());
        ClassName dafnyEnumClass = dafnyNameResolver.classForShape(shape);

        MethodSpec.Builder builder = MethodSpec
                .methodBuilder(methodName)
                .addModifiers(Modifier.STATIC, Modifier.PUBLIC)
                .returns(dafnyEnumClass)
                //should be String nativeValue
                .addParameter(nativeNameResolver.typeForShape(shapeId), "nativeValue");
        builder.addStatement(
                "return $L($T.fromValue(nativeValue))",
                methodName,
                nativeNameResolver.classForEnum(shape)
        );

        return builder.build();
    }

    MethodSpec generateConvertEnumEnum(ShapeId shapeId) {
        final StringShape shape = model.expectShape(shapeId, StringShape.class);
        String methodName = capitalize(shapeId.getName());
        final EnumTrait enumTrait = shape.getTrait(EnumTrait.class).orElseThrow();
        if (!enumTrait.hasNames()) {
            throw new UnsupportedOperationException("Unnamed enums not supported");
        }
        ClassName dafnyEnumClass = dafnyNameResolver.classForShape(shape);

        MethodSpec.Builder builder = MethodSpec
                .methodBuilder(methodName)
                .addModifiers(Modifier.STATIC, Modifier.PUBLIC)
                .returns(dafnyEnumClass)
                .addParameter(nativeNameResolver.classForEnum(shape), "nativeValue")
                .beginControlFlow("switch (nativeValue)");

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
                        .beginControlFlow("case $L:", name)
                        .addStatement(
                                "return $T.$L()", dafnyEnumClass, Dafny.enumCreate(name))
                        .endControlFlow()
                );

        builder.beginControlFlow("default:")
                .addStatement(
                        "throw new $T($S + nativeValue + $S)",
                        RuntimeException.class,
                        "Cannot convert ",
                        " to %s.".formatted(dafnyEnumClass.canonicalName()))
                .endControlFlow();
        builder.endControlFlow();
        return builder.build();
    }

    /** This method:
     * 1. Determines the Shape Type
     * 2. invokes the correct generate for that shape type
     **/
    Optional<MethodSpec> generateConvert(final ShapeId shapeId) {
        final Shape shape = model.getShape(shapeId)
                .orElseThrow(() -> new IllegalStateException("Cannot find shape " + shapeId));
        // Special Enum Case
        if (shape.hasTrait(EnumTrait.class)) {
            enumShapes.add(shape);
            return Optional.empty();
        }
        return switch (shape.getType()) {
            case LIST -> Optional.of(generateConvertList(shape.asListShape().get()));
            case MAP -> Optional.of(generateConvertMap(shape.asMapShape().get()));
            case SET -> Optional.of(generateConvertSet(shape.asSetShape().get()));
            case STRUCTURE -> Optional.of(generateConvertStructure(shapeId));
            default -> throw new UnsupportedOperationException(
                    "ShapeId %s is of Type %s, which is not yet supported for ToDafny"
                            .formatted(shapeId, shape.getType()));
        };
    }

    /**
     * Should be called for all of a service's operations' outputs.
     */
    MethodSpec generateConvertResponse(final ShapeId shapeId) {
        MethodSpec structure = generateConvertStructure(shapeId);
        MethodSpec.Builder builder = structure.toBuilder();
        builder.parameters.clear();
        builder.addParameter(nativeNameResolver.typeForOperationOutput(shapeId), "nativeValue");
        return builder.build();
    }


    MethodSpec generateConvertStructure(final ShapeId shapeId) {
        final StructureShape structureShape = model.expectShape(shapeId, StructureShape.class);
        String methodName = capitalize(shapeId.getName());
        MethodSpec.Builder builder = MethodSpec
                .methodBuilder(methodName)
                .addModifiers(Modifier.STATIC, Modifier.PUBLIC)
                .returns(dafnyNameResolver.typeForShape(shapeId))
                .addParameter(nativeNameResolver.typeForStructure(structureShape), "nativeValue");

        if (structureShape.members().size() == 0) {
            builder.addStatement("return new $T()", dafnyNameResolver.typeForShape(shapeId));
            return builder.build();
        }

        List<CodeBlock> variables = new ArrayList<>(structureShape.members().size());
        structureShape.members().forEach(memberShape ->
                {
                    CodeBlock variable = CodeBlock.of("$L", uncapitalize(memberShape.getMemberName()));
                    builder.addStatement(memberDeclaration(memberShape, variable));
                    builder.addStatement(memberAssignment(memberShape, variable));
                    variables.add(variable);
                }
        );
        builder.addStatement("return new $T($L)",
                dafnyNameResolver.typeForShape(shapeId),
                CodeBlock.join(variables, ",")
        );
        return builder.build();
    }

    CodeBlock memberDeclaration(final MemberShape memberShape, CodeBlock variable) {
        if (memberShape.hasTrait(RequiredTrait.class) && !memberShape.hasTrait(BoxTrait.class)) {
            return CodeBlock.of("$T $L",
                    dafnyNameResolver.typeForShape(memberShape.getId()),
                    variable
            );
        }
        return CodeBlock.of("$T $L",
                ParameterizedTypeName.get(
                        ClassName.get("Wrappers_Compile", "Option"),
                        dafnyNameResolver.typeForShape(memberShape.getId())),
                variable);
    }

    CodeBlock memberAssignment(final MemberShape memberShape, CodeBlock variable) {
        CodeBlock getMember = getMember(CodeBlock.of("nativeValue"), memberShape);
        if (memberShape.hasTrait(RequiredTrait.class) && !memberShape.hasTrait(BoxTrait.class)) {
            return CodeBlock.of(
                    "$L = $L",
                    variable,
                    memberConversion(memberShape, getMember)
            );
        }
        return CodeBlock.of(
                "$L = $T.nonNull($L) ?\n$T.create_Some($L)\n: $T.create_None()",
                variable,
                ClassName.get(Objects.class),
                getMember,
                ClassName.get("Wrappers_Compile", "Option"),
                memberConversion(memberShape, getMember),
                ClassName.get("Wrappers_Compile", "Option")
        );
    }

    /** For AWS SDK structure members, the getter is `get + capitalized member name`. */
    CodeBlock getMember(CodeBlock variableName, MemberShape memberShape) {
        return CodeBlock.of("$L.get$L()", variableName, capitalize(memberShape.getMemberName()));
    }

    /** CodeBlock invoking the member conversion method. */
    CodeBlock memberConversion(MemberShape memberShape, CodeBlock getMemberCall) {
        return CodeBlock.of("$L($L)",
                memberConversionMethodReference(memberShape).asNormalReference(),
                getMemberCall
        );
    }

    /**
     * Returns MethodReference that converts from
     * the Java Native memberShape to
     * the Java Dafny memberShape.
     * Side Effects:
     * If in namespace and Shape is not simple,
     * adds Shape to additional converters.
     */
    MethodReference memberConversionMethodReference(final MemberShape memberShape) {
        Shape target = model.getShape(memberShape.getTarget()).get();
        // If the target is simple, use SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE
        if (ModelUtils.isSmithyApiOrSimpleShape(target)) {
            if (Dafny.UNSUPPORTED_SHAPES.contains(target.getType())) {
                throw new UnsupportedOperationException(
                        "No converter for %s written yet.".formatted(target.getType())
                );
            }
            return SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(target.getType());
        }
        final String methodName = capitalize(target.getId().getName());
        // if in namespace
        if (nativeNameResolver.isInServiceNameSpace(target.getId())) {
            // add to additionalShapes,
            additionalShapes.add(target);
            // and reference to be created converter
            return new MethodReference(thisClassName, methodName);
        }
        // Otherwise, this target must be in another namespace
        ClassName otherNamespaceToDafny = ClassName.get(target.getId().getNamespace(), "ToDafny");
        return new MethodReference(otherNamespaceToDafny, methodName);
    }

    MethodSpec generateConvertList(ListShape shape) {
        MemberShape memberShape = shape.getMember();
        CodeBlock memberConverter = memberConversionMethodReference(memberShape).asFunctionalReference();
        CodeBlock genericCall = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(shape.getType()).asNormalReference();
        // I am not sure that this typeDescriptor look up logic will always work
        MethodReference getTypeDescriptor = new MethodReference(
                dafnyNameResolver.classForShape(memberShape.getTarget()),
                "_typeDescriptor");
        ParameterSpec parameterSpec = ParameterSpec
                .builder(nativeNameResolver.typeForShape(shape.getId()), "nativeValue")
                .build();
        return MethodSpec
                .methodBuilder(StringUtils.capitalize(shape.getId().getName()))
                .addModifiers(Modifier.PUBLIC, Modifier.STATIC)
                .returns(dafnyNameResolver.typeForAggregateWithWildcard(shape.getId()))
                .addParameter(parameterSpec)
                .addStatement("return $L(nativeValue, $L, $L())",
                        genericCall, memberConverter, getTypeDescriptor.asNormalReference())
                .build();
    }

    MethodSpec generateConvertSet(SetShape shape) {
        MemberShape memberShape = shape.getMember();
        CodeBlock memberConverter = memberConversionMethodReference(memberShape).asFunctionalReference();
        CodeBlock genericCall = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(shape.getType()).asNormalReference();
        ParameterSpec parameterSpec = ParameterSpec
                .builder(nativeNameResolver.typeForShape(shape.getId()), "nativeValue")
                .build();
        return MethodSpec
                .methodBuilder(StringUtils.capitalize(shape.getId().getName()))
                .addModifiers(Modifier.PUBLIC, Modifier.STATIC)
                .returns(dafnyNameResolver.typeForAggregateWithWildcard(shape.getId()))
                .addParameter(parameterSpec)
                .addStatement("return $L(nativeValue, $L)",
                        genericCall, memberConverter)
                .build();
    }

    MethodSpec generateConvertMap(MapShape shape) {
        MemberShape keyShape = shape.getKey().asMemberShape().get();
        CodeBlock keyConverter = memberConversionMethodReference(keyShape).asFunctionalReference();
        MemberShape valueShape = shape.getValue().asMemberShape().get();
        CodeBlock valueConverter = memberConversionMethodReference(valueShape).asFunctionalReference();
        CodeBlock genericCall = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(shape.getType()).asNormalReference();
        ParameterSpec parameterSpec = ParameterSpec
                .builder(nativeNameResolver.typeForShape(shape.getId()), "nativeValue")
                .build();
        return MethodSpec
                .methodBuilder(StringUtils.capitalize(shape.getId().getName()))
                .addModifiers(Modifier.PUBLIC, Modifier.STATIC)
                .returns(dafnyNameResolver.typeForAggregateWithWildcard(shape.getId()))
                .addParameter(parameterSpec)
                .addStatement("return $L(nativeValue, $L, $L)",
                        genericCall, keyConverter, valueConverter)
                .build();
    }


    /**  */
    MethodSpec generateConvertError(final ShapeId shapeId) {
        MethodSpec structure = generateConvertStructure(shapeId);
        MethodSpec.Builder builder = structure.toBuilder();
        builder.setName("Error");
        return builder.build();
    }

    MethodSpec generateConvertOpaqueError() {
        // TODO: This is a hack, but so are opaque errors, they are not in our smithy models!!
        return MethodSpec.methodBuilder("Error")
                .addModifiers(Modifier.PUBLIC, Modifier.STATIC)
                .returns(dafnyNameResolver.getDafnyAbstractServiceError())
                .addParameter(nativeNameResolver.baseErrorForService(), "nativeValue")
                .addStatement("Option<DafnySequence<? extends Character>> message")
                .addStatement("""
                        message = Objects.nonNull(nativeValue.getMessage()) ?
                                        create_Some(CharacterSequence(nativeValue.getMessage()))
                                        : create_None()""")
                .addStatement("return new $T(message)", dafnyNameResolver.getDafnyAbstractServiceError())
                .build();
    }

    /**
     * The keys are the input type,
     * the values are the method that converts
     * from that input to the Dafny type
     */
    static final Map<ShapeType, MethodReference> AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE;
    static final Map<ShapeType, MethodReference> SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE;
    static final ClassName COMMON_TO_DAFNY_SIMPLE = ClassName.get(software.amazon.dafny.conversion.ToDafny.Simple.class);
    static final ClassName COMMON_TO_DAFNY_AGGREGATE = ClassName.get(software.amazon.dafny.conversion.ToDafny.Aggregate.class);

    static {
        AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE = Map.ofEntries(
                Map.entry(ShapeType.LIST, new MethodReference(COMMON_TO_DAFNY_AGGREGATE, "GenericToSequence")),
                Map.entry(ShapeType.SET, new MethodReference(COMMON_TO_DAFNY_AGGREGATE,"GenericToSet")),
                Map.entry(ShapeType.MAP, new MethodReference(COMMON_TO_DAFNY_AGGREGATE,"GenericToMap"))
        );
        SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE = Map.ofEntries(
                Map.entry(ShapeType.BLOB, new MethodReference(COMMON_TO_DAFNY_SIMPLE, "ByteSequence")),
                Map.entry(ShapeType.BOOLEAN, Constants.IDENTITY_FUNCTION),
                Map.entry(ShapeType.STRING, new MethodReference(COMMON_TO_DAFNY_SIMPLE, "CharacterSequence")),
                Map.entry(ShapeType.TIMESTAMP, new MethodReference(COMMON_TO_DAFNY_SIMPLE, "CharacterSequence")),
                Map.entry(ShapeType.BYTE, Constants.IDENTITY_FUNCTION),
                Map.entry(ShapeType.SHORT, Constants.IDENTITY_FUNCTION),
                Map.entry(ShapeType.INTEGER, Constants.IDENTITY_FUNCTION),
                Map.entry(ShapeType.LONG, Constants.IDENTITY_FUNCTION),
                Map.entry(ShapeType.BIG_DECIMAL, Constants.IDENTITY_FUNCTION),
                Map.entry(ShapeType.BIG_INTEGER, Constants.IDENTITY_FUNCTION)
        );
    }

}
