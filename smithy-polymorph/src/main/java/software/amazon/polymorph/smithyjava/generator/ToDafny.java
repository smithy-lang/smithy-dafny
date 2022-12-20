package software.amazon.polymorph.smithyjava.generator;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.ParameterSpec;
import com.squareup.javapoet.ParameterizedTypeName;
import com.squareup.javapoet.TypeName;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

import javax.lang.model.element.Modifier;

import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.polymorph.smithyjava.NamespaceHelper;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.utils.ModelUtils;

import software.amazon.smithy.model.shapes.ListShape;
import software.amazon.smithy.model.shapes.MapShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.SetShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ShapeType;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.UnionShape;
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
    /**
     * The class name of the Subject's Shim's ToDafny class.
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
                .addParameter(subject.nativeNameResolver.classNameForStructure(structureShape), VAR_INPUT);

        if (structureShape.members().size() == 0) {
            builder.addStatement("return new $T()", subject.dafnyNameResolver.typeForShape(shapeId));
            return builder.build();
        }
        List<CodeBlock> variables = new ArrayList<>(structureShape.members().size());
        structureShape.members().forEach(memberShape ->
                {
                    CodeBlock varOut = CodeBlock.of("$L", uncapitalize(memberShape.getMemberName()));
                    CodeBlock varIn = getMember(CodeBlock.of(VAR_INPUT), memberShape);
                    builder.addStatement(memberDeclaration(memberShape, varOut));
                    builder.addStatement(memberAssignment(memberShape, varOut, varIn));
                    variables.add(varOut);
                }
        );
        builder.addStatement("return new $T($L)",
                subject.dafnyNameResolver.typeForShape(shapeId),
                CodeBlock.join(variables, ", ")
        );
        return builder.build();
    }

    protected MethodSpec modeledUnion(final UnionShape shape) {
        final ShapeId shapeId = shape.getId();
        String methodName = capitalize(shape.getId().getName());
        TypeName returnType = subject.dafnyNameResolver.typeForShape(shapeId);
        MethodSpec.Builder method = MethodSpec
                .methodBuilder(methodName)
                .addModifiers(PUBLIC_STATIC)
                .returns(returnType)
                .addParameter(subject.nativeNameResolver.classNameForStructure(shape), VAR_INPUT);
        // TODO: Once dafny always generates create_<datatypeConstructor>, remove this if block
        if (shape.members().size() == 1) {
            // There is one, stream().findFirst will return a value
            //noinspection OptionalGetWithoutIsPresent
            MemberShape onlyMember = shape.members().stream().findFirst().get();
            CodeBlock getField = CodeBlock.of("$L.$L()", VAR_INPUT, onlyMember.getMemberName());
            CodeBlock memberConversion = memberConversion(onlyMember, getField);
            method.addStatement("return $T.create($L)", returnType, memberConversion);
            return method.build();
        }
        shape.members().forEach(member -> {
            CodeBlock getField = CodeBlock.of("$L.$L()", VAR_INPUT, member.getMemberName());
            CodeBlock memberConversion = memberConversion(member, getField);
            String datatypeConstructorCreate = Dafny.datatypeConstructorCreate(member.getMemberName());
            method.beginControlFlow("if ($T.nonNull($L))", Objects.class, getField)
                    .addStatement("return $T.$L($L)", returnType, datatypeConstructorCreate, memberConversion)
                    .endControlFlow();
        });
        method.addStatement(
                "throw new $T($S + $L + $S)",
                IllegalArgumentException.class,
                "Cannot convert ",
                VAR_INPUT,
                " to %s.".formatted(returnType));
        return method.build();
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

    /** @return CodeBlock assigning result of member conversion to variable. */
    protected CodeBlock memberAssignment(
            final MemberShape memberShape,
            CodeBlock outputVar,
            CodeBlock inputVar
    ) {
        if (memberShape.isRequired()) {
            return CodeBlock.of(
                    "$L = $L",
                    outputVar,
                    memberConversion(memberShape, inputVar)
            );
        }
        return CodeBlock.of(
                "$L = $T.nonNull($L) ?\n$T.create_Some($L)\n: $T.create_None()",
                outputVar,
                ClassName.get(Objects.class),
                inputVar,
                ClassName.get("Wrappers_Compile", "Option"),
                memberConversion(memberShape, inputVar),
                ClassName.get("Wrappers_Compile", "Option")
        );
    }

    @SuppressWarnings("OptionalGetWithoutIsPresent")
    protected MethodSpec modeledEnum(StringShape shape) {
        final ShapeId shapeId = shape.getId();
        String methodName = capitalize(shapeId.getName());
        final EnumTrait enumTrait = shape.getTrait(EnumTrait.class).orElseThrow(
                () -> new IllegalArgumentException(
                        "Shape must have the enum trait. ShapeId: %s".formatted(shapeId))
        );
        if (!enumTrait.hasNames()) {
            throw new UnsupportedOperationException(
                    "Unnamed enums not supported. ShapeId: %s".formatted(shapeId));
        }
        TypeName dafnyEnumClass = subject.dafnyNameResolver.typeForShape(shapeId);

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
                                "return $T.$L()", dafnyEnumClass, Dafny.datatypeConstructorCreate(name))
                        .endControlFlow()
                );

        builder.beginControlFlow("default:")
                .addStatement(
                        "throw new $T($S + $L + $S)",
                        RuntimeException.class,
                        "Cannot convert ",
                        VAR_INPUT,
                        " to %s.".formatted(dafnyEnumClass))
                .endControlFlow();
        builder.endControlFlow();
        return builder.build();
    }

    protected MethodSpec modeledList(ListShape shape) {
        MemberShape memberShape = shape.getMember();
        CodeBlock memberConverter = memberConversionMethodReference(memberShape).asFunctionalReference();
        CodeBlock genericCall = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(shape.getType()).asNormalReference();
        CodeBlock getTypeDescriptor = subject.dafnyNameResolver.typeDescriptor(memberShape.getTarget());
        ParameterSpec parameterSpec = ParameterSpec
                .builder(subject.nativeNameResolver.typeForShape(shape.getId()), "nativeValue")
                .build();
        return MethodSpec
                .methodBuilder(capitalize(shape.getId().getName()))
                .addModifiers(Modifier.PUBLIC, Modifier.STATIC)
                .returns(subject.dafnyNameResolver.typeForAggregateWithWildcard(shape.getId()))
                .addParameter(parameterSpec)
                .addStatement("return $L(\nnativeValue, \n$L, \n$L)",
                        genericCall, memberConverter, getTypeDescriptor)
                .build();
    }

    protected MethodSpec modeledSet(SetShape shape) {
        MemberShape memberShape = shape.getMember();
        CodeBlock memberConverter = memberConversionMethodReference(memberShape).asFunctionalReference();
        CodeBlock genericCall = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(shape.getType()).asNormalReference();
        ParameterSpec parameterSpec = ParameterSpec
                .builder(subject.nativeNameResolver.typeForShape(shape.getId()), "nativeValue")
                .build();
        return MethodSpec
                .methodBuilder(capitalize(shape.getId().getName()))
                .addModifiers(Modifier.PUBLIC, Modifier.STATIC)
                .returns(subject.dafnyNameResolver.typeForAggregateWithWildcard(shape.getId()))
                .addParameter(parameterSpec)
                .addStatement("return $L(\nnativeValue, \n$L)",
                        genericCall, memberConverter)
                .build();
    }

    @SuppressWarnings("OptionalGetWithoutIsPresent")
    protected MethodSpec modeledMap(MapShape shape) {
        MemberShape keyShape = shape.getKey().asMemberShape().get();
        CodeBlock keyConverter = memberConversionMethodReference(keyShape).asFunctionalReference();
        MemberShape valueShape = shape.getValue().asMemberShape().get();
        CodeBlock valueConverter = memberConversionMethodReference(valueShape).asFunctionalReference();
        CodeBlock genericCall = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(shape.getType()).asNormalReference();
        ParameterSpec parameterSpec = ParameterSpec
                .builder(subject.nativeNameResolver.typeForShape(shape.getId()), "nativeValue")
                .build();
        return MethodSpec
                .methodBuilder(capitalize(shape.getId().getName()))
                .addModifiers(Modifier.PUBLIC, Modifier.STATIC)
                .returns(subject.dafnyNameResolver.typeForAggregateWithWildcard(shape.getId()))
                .addParameter(parameterSpec)
                .addStatement("return $L(\nnativeValue, \n$L, \n$L)",
                        genericCall, keyConverter, valueConverter)
                .build();
    }

    /** AWS SDK V1 uses a different getter pattern than Library (or, possibly, SDK V2) */
    abstract protected CodeBlock getMember(CodeBlock variableName, MemberShape memberShape);

    /** CodeBlock invoking the member conversion method. */
    protected CodeBlock memberConversion(MemberShape memberShape, CodeBlock inputVar) {

        // TODO unshippable
        CodeBlock methodBlock = memberConversionMethodReference(memberShape).asNormalReference();

        return CodeBlock.of("$L($L)",
            methodBlock,
            transformInputVarForMemberConversion(methodBlock, inputVar)
        );
    }

    /**
     * Transforms
     * @param methodBlock
     * @param inputVar
     * @return
     */
    public CodeBlock transformInputVarForMemberConversion(CodeBlock methodBlock, CodeBlock inputVar) {
        ClassName JAVA_UTIL_COLLECTORS = ClassName.get("java.util.stream", "Collectors");
        MethodReference collectors = new MethodReference(JAVA_UTIL_COLLECTORS, "toList");

        CodeBlock.Builder returnCodeBlockBuilder = CodeBlock.builder().add(inputVar);
        if (methodBlock.toString().contains("ByteSequence")) {
            CodeBlock asByteArray = CodeBlock.of("asByteArray()");
            return returnCodeBlockBuilder.add(".asByteArray()").build();
        }
        if (methodTypeRequiresStringConversion(methodBlock)) {
            return returnCodeBlockBuilder
                .add(".stream().map(Object::toString).collect(")
                .add(collectors.asNormalReference())
                .add("())")
                .build();
        }
        return inputVar;
    }

    /**
     * Returns true if the method name indicates the type requires conversion to String.
     * Some AWS SDK V2 types now require explicit String conversion, while they didn't in V1.
     * @return true if the method name indicates the type requires conversion to String; false otherwise
     */
    protected boolean methodTypeRequiresStringConversion(CodeBlock methodBlock) {
        return methodBlock.toString().contains("EncryptionAlgorithmSpecList")
            || methodBlock.toString().contains("SigningAlgorithmSpecList")
            || methodBlock.toString().contains("GrantOperationList")
    }

    /**
     * Returns MethodReference that converts from
     * the Java Native memberShape to
     * the Java Dafny memberShape.
     */
    @SuppressWarnings({"DuplicatedCode"})
    protected MethodReference memberConversionMethodReference(final MemberShape memberShape) {
        Shape targetShape = subject.model.expectShape(memberShape.getTarget());
        // If the target is simple, use SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE
        if (ModelUtils.isSmithyApiOrSimpleShape(targetShape)) {
            return SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(targetShape.getType());
        }
        final String methodName = capitalize(targetShape.getId().getName());
        // if in namespace, reference converter from this ToDafny class
        if (subject.nativeNameResolver.isInServiceNameSpace(targetShape.getId())) {
            return new MethodReference(thisClassName, methodName);
        }
        // Otherwise, this target must be in another namespace,
        // reference converter from that namespace's ToDafny class
        ClassName otherNamespaceToDafny = ClassName.get(
                NamespaceHelper.standardize(targetShape.getId().getNamespace()),
                TO_DAFNY);
        return new MethodReference(otherNamespaceToDafny, methodName);
    }

    protected MethodSpec modeledError(final StructureShape shape) {
        MethodSpec structure = modeledStructure(shape);
        MethodSpec.Builder builder = structure.toBuilder();
        builder.setName("Error");
        builder.returns(subject.dafnyNameResolver.abstractClassForError());
        return builder.build();
    }
}
