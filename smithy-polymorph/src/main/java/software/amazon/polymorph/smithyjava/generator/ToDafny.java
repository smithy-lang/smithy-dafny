package software.amazon.polymorph.smithyjava.generator;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.ParameterizedTypeName;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

import javax.lang.model.element.Modifier;

import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.utils.DafnyNameResolverHelpers;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ShapeType;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.EnumDefinition;
import software.amazon.smithy.model.traits.EnumTrait;

import static software.amazon.smithy.utils.StringUtils.capitalize;
import static software.amazon.smithy.utils.StringUtils.uncapitalize;

public abstract class ToDafny extends Generator {
    /**
     * The keys are the input type, the values are the method that converts from that input to the Dafny type
     */
    protected static final Map<ShapeType, MethodReference> AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE;
    protected static final Map<ShapeType, MethodReference> SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE;
    protected static final ClassName COMMON_TO_DAFNY_SIMPLE = ClassName.get(software.amazon.dafny.conversion.ToDafny.Simple.class);
    protected static final ClassName COMMON_TO_DAFNY_AGGREGATE = ClassName.get(software.amazon.dafny.conversion.ToDafny.Aggregate.class);
    protected final static String VAR_INPUT = "nativeValue";
    protected static final String TO_DAFNY = "ToDafny";
    protected static final Modifier[] PUBLIC_STATIC = new Modifier[]{Modifier.PUBLIC, Modifier.STATIC};
    /**
     * The class name of the AWS SDK's Service's Shim's ToDafny class.
     */
    protected final ClassName thisClassName;

    public ToDafny(CodegenSubject subject, ClassName className) {
        super(subject);
        thisClassName = className;
    }

    static {
        AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE = Map.ofEntries(
                Map.entry(ShapeType.LIST, new MethodReference(COMMON_TO_DAFNY_AGGREGATE, "GenericToSequence")),
                Map.entry(ShapeType.SET, new MethodReference(COMMON_TO_DAFNY_AGGREGATE, "GenericToSet")),
                Map.entry(ShapeType.MAP, new MethodReference(COMMON_TO_DAFNY_AGGREGATE, "GenericToMap"))
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

    protected MethodSpec modeledStructure(
            final StructureShape structureShape
    ) {
        final ShapeId shapeId = structureShape.getId();
        String methodName = capitalize(structureShape.getId().getName());
        MethodSpec.Builder builder = MethodSpec
                .methodBuilder(methodName)
                .addModifiers(PUBLIC_STATIC)
                .returns(subject.dafnyNameResolver.typeForShape(shapeId))
                .addParameter(subject.nativeNameResolver.typeForStructure(structureShape), VAR_INPUT);

        if (structureShape.members().size() == 0) {
            builder.addStatement("return new $T()", subject.dafnyNameResolver.typeForShape(shapeId));
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
                subject.dafnyNameResolver.typeForShape(shapeId),
                CodeBlock.join(variables, ", ")
        );
        return builder.build();
    }

    protected CodeBlock memberDeclaration(final MemberShape memberShape, CodeBlock variable) {
        if (memberShape.isRequired()) {
            return CodeBlock.of("$T $L",
                    subject.dafnyNameResolver.typeForShape(memberShape.getId()),
                    variable
            );
        }
        return CodeBlock.of("$T $L",
                ParameterizedTypeName.get(
                        ClassName.get("Wrappers_Compile", "Option"),
                        subject.dafnyNameResolver.typeForShape(memberShape.getId())),
                variable);
    }

    protected CodeBlock memberAssignment(final MemberShape memberShape, CodeBlock variable) {
        CodeBlock getMember = getMember(CodeBlock.of(VAR_INPUT), memberShape);
        if (memberShape.isRequired()) {
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

    @SuppressWarnings("OptionalGetWithoutIsPresent")
    protected MethodSpec modeledEnum(StringShape shape) {
        final ShapeId shapeId = shape.getId();
        String methodName = capitalize(shapeId.getName());
        final EnumTrait enumTrait = shape.getTrait(EnumTrait.class).orElseThrow();
        if (!enumTrait.hasNames()) {
            throw new UnsupportedOperationException("Unnamed enums not supported");
        }
        ClassName dafnyEnumClass = subject.dafnyNameResolver.classForShape(shape);

        MethodSpec.Builder builder = MethodSpec
                .methodBuilder(methodName)
                .addModifiers(Modifier.STATIC, Modifier.PUBLIC)
                .returns(dafnyEnumClass)
                .addParameter(subject.nativeNameResolver.classForEnum(shape), VAR_INPUT)
                .beginControlFlow("switch ($L)", VAR_INPUT);

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
                        "throw new $T($S + $L + $S)",
                        RuntimeException.class,
                        "Cannot convert ",
                        VAR_INPUT,
                        " to %s.".formatted(dafnyEnumClass.canonicalName()))
                .endControlFlow();
        builder.endControlFlow();
        return builder.build();
    }

    /** AWS SDK V1 uses a different getter pattern than Library (or, possibly, SDK V2) */
    abstract protected CodeBlock getMember(CodeBlock variableName, MemberShape memberShape);

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
     */
    @SuppressWarnings({"DuplicatedCode", "OptionalGetWithoutIsPresent"})
    protected MethodReference memberConversionMethodReference(final MemberShape memberShape) {
        Shape targetShape = subject.model.getShape(memberShape.getTarget()).get();
        // If the target is simple, use SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE
        if (ModelUtils.isSmithyApiOrSimpleShape(targetShape)) {
            return SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(targetShape.getType());
        }
        final String methodName = capitalize(targetShape.getId().getName());
        // if in namespace, reference to be created converter
        if (subject.nativeNameResolver.isInServiceNameSpace(targetShape.getId())) {
            return new MethodReference(thisClassName, methodName);
        }
        // Otherwise, this target must be in another namespace
        ClassName otherNamespaceToDafny = ClassName.get(
                DafnyNameResolverHelpers.packageNameForNamespace(targetShape.getId().getNamespace()),
                TO_DAFNY);
        return new MethodReference(otherNamespaceToDafny, methodName);
    }

    protected MethodSpec modeledError(final StructureShape shape) {
        MethodSpec structure = modeledStructure(shape);
        MethodSpec.Builder builder = structure.toBuilder();
        builder.setName("Error");
        builder.returns(subject.dafnyNameResolver.getDafnyAbstractServiceError());
        return builder.build();
    }
}
