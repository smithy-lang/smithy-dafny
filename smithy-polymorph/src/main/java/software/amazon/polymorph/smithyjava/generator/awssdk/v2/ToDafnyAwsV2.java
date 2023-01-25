package software.amazon.polymorph.smithyjava.generator.awssdk.v2;

import com.squareup.javapoet.AnnotationSpec;
import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.ParameterSpec;
import com.squareup.javapoet.ParameterizedTypeName;
import com.squareup.javapoet.TypeName;
import com.squareup.javapoet.TypeSpec;
import com.squareup.javapoet.WildcardTypeName;

import java.util.Collection;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import javax.lang.model.element.Modifier;

import dafny.DafnySequence;
import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.polymorph.smithyjava.generator.ToDafny;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
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
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.model.traits.EnumDefinition;
import software.amazon.smithy.model.traits.EnumTrait;

import static software.amazon.polymorph.smithyjava.generator.Generator.Constants.JAVA_UTIL_STREAM_COLLECTORS;
import static software.amazon.smithy.utils.StringUtils.capitalize;

/**
 * ToDafnyAwsV2 generates ToDafny.
 * ToDafny is a helper class for the AwsSdk's {@link ShimV2}.<p>
 * It holds methods to convert
 * a subset of an AWS SDK Service's types to Dafny types.<p>
 * The subset is composed of:
 * <ul>
 *   <li>All the Service's Operations' outputs
 *   <li>All the Service's Errors
 *   <li>All the fields contained by the above
 * </ul>
 * As such,
 * ToDafnyAwsV2 holds the logic to generate these methods based on:
 * <ul>
 *     <li>a smithy model</li>
 *     <li>knowledge of how smithy-dafny generates Dafny for AWS SDK</li>
 *     <li>knowledge of how Dafny compiles Java</li>
 *     <li>knowledge of the patterns of the AWS SDK V2 for Java</li>
 * </ul>
 */
public class ToDafnyAwsV2 extends ToDafny {
    // Hack to override subject to JavaAwsSdkV2
    // See code comment on ../library/ModelCodegen for details.
    final JavaAwsSdkV2 subject;

    public ToDafnyAwsV2(JavaAwsSdkV2 awsSdk) {
        super(
                awsSdk,
                //TODO: JavaAwsSdkV2 should really have a declared packageName, not rely on the name resolver
                ClassName.get(awsSdk.dafnyNameResolver.packageName(), TO_DAFNY));

        this.subject = awsSdk;
    }

    @Override
    public Set<JavaFile> javaFiles() {
        JavaFile.Builder builder = JavaFile
                .builder(subject.dafnyNameResolver.packageName(), toDafny());
        return Collections.singleton(builder.build());
    }

    TypeSpec toDafny() {
        LinkedHashSet<ShapeId> operationOutputs = subject.serviceShape
                .getOperations().stream()
                .map(shapeId -> subject.model.expectShape(shapeId, OperationShape.class))
                .map(OperationShape::getOutput).filter(Optional::isPresent).map(Optional::get)
                .collect(Collectors.toCollection(LinkedHashSet::new));

        // OperationErrors are streamed to gather the types that are only inputs or outputs to errors.
        // Right now this is only CancellationReasonList.
        LinkedHashSet<ShapeId> operationErrors = subject.serviceShape
            .getOperations().stream()
            .map(shapeId -> subject.model.expectShape(shapeId, OperationShape.class))
            .map(OperationShape::getErrors)
            .flatMap(Collection::stream)
            .filter(structureShape -> !structureShape.toString().contains("InvalidEndpointException"))
            .collect(Collectors.toCollection(LinkedHashSet::new));
        operationOutputs.addAll(operationErrors); // TODO

        Set<ShapeId> allRelevantShapeIds = ModelUtils.findAllDependentShapes(operationOutputs, subject.model);

        // In the AWS SDK for Java V2, Operation Outputs are special
        allRelevantShapeIds.removeAll(operationOutputs);

        // Enums are also a special case
        LinkedHashSet<ShapeId> enumShapeIds = new LinkedHashSet<>();
        allRelevantShapeIds.forEach(shapeId -> {
            Shape shape = subject.model.expectShape(shapeId);
            if (shape.hasTrait(EnumTrait.class)) {
                enumShapeIds.add(shapeId);
            }
        });
        allRelevantShapeIds.removeAll(enumShapeIds);

        final List<MethodSpec> convertOutputs = operationOutputs.stream()
                .map(this::generateConvert).toList();
        final List<MethodSpec> convertAllRelevant = allRelevantShapeIds.stream()
                .map(this::generateConvert).filter(Objects::nonNull).toList();
        final List<MethodSpec> convertServiceErrors = ModelUtils.streamServiceErrors(subject.model, subject.serviceShape)
            // InvalidEndpointException does not exist in SDK V2
            .filter(structureShape -> !structureShape.getId().getName().contains("InvalidEndpointException"))
            .map(this::modeledError).collect(Collectors.toList());
        convertServiceErrors.add(generateConvertOpaqueError());

        // For enums, we generate overloaded methods,
        // one to convert instances of the Enum
        final List<MethodSpec> convertEnumEnum = enumShapeIds
                .stream().map(this::generateConvertEnumEnum).toList();
        // The other to convert String representatives of the enum
        final List<MethodSpec> convertEnumString = enumShapeIds
                .stream().map(this::generateConvertEnumString).toList();

        return TypeSpec
                .classBuilder(
                        ClassName.get(subject.dafnyNameResolver.packageName(), "ToDafny"))
                .addModifiers(Modifier.PUBLIC)
                .addMethods(convertOutputs)
                .addMethods(convertAllRelevant)
                .addMethods(convertServiceErrors)
                .addMethods(convertEnumEnum)
                .addMethods(convertEnumString)
                .build();
    }

    /** This method:
     * 1. Determines the Shape Type
     * 2. invokes the correct generate for that shape type
     */
    @SuppressWarnings({"OptionalGetWithoutIsPresent", "DuplicatedCode"})
    MethodSpec generateConvert(final ShapeId shapeId) {
        final Shape shape = subject.model.getShape(shapeId)
                .orElseThrow(() -> new IllegalStateException("Cannot find shape " + shapeId));

        return switch (shape.getType()) {
            // For the AWS SDK for Java, we do not generate converters for simple shapes
            case BLOB, BOOLEAN, STRING, TIMESTAMP, BYTE, SHORT,
                    INTEGER, LONG, BIG_DECIMAL, BIG_INTEGER, MEMBER -> null;
            case LIST -> modeledList(shape.asListShape().get());
            case MAP -> modeledMap(shape.asMapShape().get());
            case SET -> modeledSet(shape.asSetShape().get());
            case STRUCTURE -> generateConvertStructure(shapeId);
            case UNION -> generateConvertUnion(shapeId);
            default -> throw new UnsupportedOperationException(
                "ShapeId %s is of Type %s, which is not yet supported for ToDafny"
                    .formatted(shapeId, shape.getType()));
        };
    }

    MethodSpec generateConvertUnion(final ShapeId shapeId) {
        final UnionShape unionShape = subject.model.expectShape(shapeId, UnionShape.class);
        return super.modeledUnion(unionShape);
    }

    @Override
    protected CodeBlock memberConversion(MemberShape memberShape, CodeBlock inputVar) {
        CodeBlock methodBlock = memberConversionMethodReference(memberShape).asNormalReference();

        return CodeBlock.of("$L($L)",
            methodBlock,
            formatInputVarForMemberConversion(memberShape, inputVar)
        );
    }

    /**
     * Formats inputVar if it requires reformatting for SDK V2.
     * @param memberShape shape defined in Smithy model
     * @param inputVar CodeBlock to be formatted. This SHOULD be used to build a formatted
     *                 CodeBlock, but SHOULD NOT be used in logic that decides HOW to build a
     *                 formatted CodeBlock.
     *                 Prefer to use MemberShape in decision logic as MemberShape is the source of
     *                 truth from the Smithy model.
     * @return inputVar formatted for SDK V2
     */
    public CodeBlock formatInputVarForMemberConversion(MemberShape memberShape, CodeBlock inputVar) {
        CodeBlock.Builder returnCodeBlockBuilder = CodeBlock.builder().add(inputVar);

        // If methodBlock is transforming to Dafny ByteSequence, it is expecting either a byte[]
        //   or ByteBuffer.
        // In this case, inputVar is of type SdkBytes.
        // dafny-java-conversion should not have a ByteSequence constructor that directly takes in
        //   SdkBytes. If it did, Polymorph would need to depend on AWS SDK for Java V2.
        // The conversion from inputVar as SdkBytes to a Dafny ByteSequence looks like
        //   ByteSequence(inputVar.asByteArray())
        Shape targetShape = subject.model.expectShape(memberShape.getTarget());
        if (targetShape.getType() == ShapeType.BLOB) {
            return returnCodeBlockBuilder
                .add(".asByteArray()")
                .build();
        }

        // BinarySetAttributeValue conversion is special.
        // The input Dafny type is DafnySequence<? extends DafnySequence<? extends Byte>>.
        // The output native type is List<SdkBytes>.
        // dafny-java-conversion can convert most input types directly to the output types;
        //     however, SdkBytes is an exception. SdkBytes is defined in the AWS SDK. It is not a
        //     native Java nor Dafny type.
        // We do not want to write a conversion to SdkBytes inside dafny-java-conversion, else
        //     Polymorph would need to take a dependency on the AWS SDK. Instead, smithy-polymorph=
        //     will generate the required conversion code.
        // This is the only time when Polymorph needs to convert a list of a Dafny type to a list
        //     of a type that Polymorph does not know about. So this is a special case and warrants
        //     its own generation logic.
        if (targetShape.getId().getName().equals("BinarySetAttributeValue")) {
            return returnCodeBlockBuilder
                .add(".stream().map((self) -> { return self.asByteBuffer(); } ).collect(\n"
                    + "$L.toList())", JAVA_UTIL_STREAM_COLLECTORS)
                .build();
        }

        // Smithy models some values as integers, but SDK expects doubles.
        // .intValue will round down; i.e. the decimal portion is removed. This mirrors Dotnet's
        //     double -> int casting.
        if (shapeRequiresTypeConversionFromDoubleToInt(targetShape.getId())) {
            return returnCodeBlockBuilder
                .add(".intValue()")
                .build();
        }

        // SizeEstimateRangeGB is a list of the case above, where Smithy models values as integers,
        //     but the SDK expects doubles.
        // This is the only instance of double -> int conversion in a list right now.
        if (memberShape.getMemberName().equals("SizeEstimateRangeGB")) {
            MethodReference convert = new MethodReference(
                JAVA_UTIL_STREAM_COLLECTORS,
                "toList");

            return returnCodeBlockBuilder
                .add(".stream()")
                .add(".map(Double::intValue)")
                .add(".collect(" + convert.asNormalReference() + "())")
                .build();
        }

        return inputVar;
    }

    /**
     * Returns true if the provided ShapeId has type integer in the Smithy model, but AWS SDK for
     *   Java V2 effectively expects type double.
     * @param shapeId
     * @return true if AWS SDK for Java V2 expects this to have been modeled as a double in Smithy
     */
    protected boolean shapeRequiresTypeConversionFromDoubleToInt(ShapeId shapeId) {
        String shapeName = shapeId.getName();

        return shapeName.equals("ConsumedCapacityUnits")
            || shapeName.equals("Double");
    }

    MethodSpec generateConvertEnumString(ShapeId shapeId) {
        final StringShape shape = subject.model.expectShape(shapeId, StringShape.class);
        String methodName = capitalize(shapeId.getName());
        TypeName dafnyEnumClass = subject.dafnyNameResolver.typeForShape(shapeId);

        MethodSpec.Builder builder = MethodSpec
                .methodBuilder(methodName)
                .addModifiers(Modifier.STATIC, Modifier.PUBLIC)
                .returns(dafnyEnumClass)
                .addParameter(subject.nativeNameResolver.classForString(), "nativeValue");
        builder.addStatement(
                "return $L($T.fromValue(nativeValue))",
                methodName,
                subject.nativeNameResolver.classForEnum(shape)
        );
        return builder.build();
    }

    protected MethodSpec generateConvertEnumEnum(ShapeId shapeId) {
        final StringShape shape = subject.model.expectShape(shapeId, StringShape.class);
        return modeledEnum(shape);
    }

    /**
     * This logic is the same as ToDafny's logic,
     * except it calls an only-defined-in-V2 formatEnumCaseName function.
     */
    @Override
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
                .beginControlFlow("case $L:",
                    subject.dafnyNameResolver.formatEnumCaseName(dafnyEnumClass, name))
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

    MethodSpec generateConvertStructure(final ShapeId shapeId) {
        final StructureShape structureShape = subject.model.expectShape(shapeId, StructureShape.class);
        return super.modeledStructure(structureShape);
    }

    @Override
    protected CodeBlock getMember(CodeBlock variableName, MemberShape memberShape) {
        return subject.dafnyNameResolver.methodForGetMember(variableName, memberShape);
    }

    /**
     * We have to customize
     * List conversion for the AWS SDK for Java V2 because
     * AWS SDK Java V2 treats Enums in a special way.
     * See the comment on
     * {@link software.amazon.polymorph.smithyjava.nameresolver.AwsSdkNativeV2#typeForShapeNoEnum}
     **/
    @Override
    protected MethodSpec modeledList(ListShape shape) {
        MemberShape memberShape = shape.getMember();
        CodeBlock memberConverter = memberConversionMethodReference(memberShape).asFunctionalReference();
        CodeBlock genericCall = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(shape.getType()).asNormalReference();
        CodeBlock getTypeDescriptor = subject.dafnyNameResolver.typeDescriptor(memberShape.getTarget());

        ParameterSpec parameterSpec = ParameterSpec
            .builder(subject.nativeNameResolver.typeForListSetOrMapNoEnum(shape.getId()), "nativeValue")
            .build();

        MethodSpec.Builder methodSpecBuilder = MethodSpec
            .methodBuilder(capitalize(shape.getId().getName()))
            .addModifiers(Modifier.PUBLIC, Modifier.STATIC)

            .returns(subject.dafnyNameResolver.typeForAggregateWithWildcard(shape.getId()))
            .addParameter(parameterSpec);

        // A static call to TypeDescriptor class requires an explicit typecast.
        // This generates an "unchecked cast" warning, which needs to be suppressed.
        // (Dafny automatically generates this warning suppression annotation for classes that
        //     generate their own _typeDescriptor() method.)
        if (subject.dafnyNameResolver.shapeIdRequiresStaticTypeDescriptor(memberShape.getTarget())) {
            return methodSpecBuilder
                // Suppress "unchecked cast" warning; this is expected
                .addAnnotation(
                    AnnotationSpec.builder(SuppressWarnings.class)
                        .addMember("value", "$S", "unchecked")
                    .build()
                )
                .addStatement("return \n($L) \n$L(\n$L, \n$L, \n$L)",
                    // This is the explicit typecast in the return statement
                    subject.dafnyNameResolver.typeForAggregateWithWildcard(shape.getId()),
                    genericCall,
                    "nativeValue",
                    memberConverter,
                    getTypeDescriptor)
                .build();
        }

        return methodSpecBuilder
                .addStatement("return $L(\n$L, \n$L, \n$L)",
                        genericCall, "nativeValue", memberConverter, getTypeDescriptor)
                .build();
    }

    /**
     * We have to customize
     * Set conversion for the AWS SDK for Java V2 because
     * AWS SDK Java V2 treats Enums in a special way.
     * See the comment on
     * {@link software.amazon.polymorph.smithyjava.nameresolver.AwsSdkNativeV2#typeForShapeNoEnum}
     **/
    @Override
    protected MethodSpec modeledSet(SetShape shape) {
        MemberShape memberShape = shape.getMember();
        CodeBlock memberConverter = memberConversionMethodReference(memberShape).asFunctionalReference();
        CodeBlock genericCall = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(shape.getType()).asNormalReference();
        ParameterSpec parameterSpec = ParameterSpec
                .builder(subject.nativeNameResolver.typeForListSetOrMapNoEnum(shape.getId()), "nativeValue")
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

    /**
     * We have to customize
     * Map conversion for the AWS SDK for Java V2 because
     * AWS SDK Java V2 treats Enums in a special way.
     * See the comment on
     * {@link software.amazon.polymorph.smithyjava.nameresolver.AwsSdkNativeV2#typeForShapeNoEnum}
     **/
    @Override
    @SuppressWarnings("OptionalGetWithoutIsPresent")
    protected MethodSpec modeledMap(MapShape shape) {
        MemberShape keyShape = shape.getKey().asMemberShape().get();
        CodeBlock keyConverter = memberConversionMethodReference(keyShape).asFunctionalReference();
        MemberShape valueShape = shape.getValue().asMemberShape().get();
        CodeBlock valueConverter = memberConversionMethodReference(valueShape).asFunctionalReference();
        CodeBlock genericCall = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(shape.getType()).asNormalReference();
        ParameterSpec parameterSpec = ParameterSpec
                .builder(subject.nativeNameResolver.typeForListSetOrMapNoEnum(shape.getId()), "nativeValue")
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

    MethodSpec generateConvertOpaqueError() {
        // Opaque Errors are not in the model,
        // so we cannot use any of our helper methods for this method.

        CodeBlock memberDeclaration = CodeBlock.of(
                "$T $L",
                ParameterizedTypeName.get(
                        ClassName.get("Wrappers_Compile", "Option"),
                        ParameterizedTypeName.get(
                                ClassName.get(DafnySequence.class),
                                WildcardTypeName.subtypeOf(Character.class))
                ),
                "message"
        );
        // This is memberAssignment from above,
        // but with calls to dafnyNameResolver replaced with their expected response.
        CodeBlock memberAssignment = CodeBlock.of(
                "$L = $T.nonNull($L) ?\n$T.create_Some($T.$L($L))\n: $T.create_None()",
                "message",
                ClassName.get(Objects.class),
                "nativeValue.getMessage()",
                ClassName.get("Wrappers_Compile", "Option"),
                COMMON_TO_DAFNY_SIMPLE,
                SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(ShapeType.STRING).methodName(),
                "nativeValue.getMessage()",
                ClassName.get("Wrappers_Compile", "Option")
        );
        return MethodSpec.methodBuilder("Error")
                .addModifiers(Modifier.PUBLIC, Modifier.STATIC)
                .returns(subject.dafnyNameResolver.abstractClassForError())
                .addParameter(subject.nativeNameResolver.baseErrorForService(), "nativeValue")
                .addStatement(memberDeclaration)
                .addStatement(memberAssignment)
                .addStatement("return new $T(message)", subject.dafnyNameResolver.classForOpaqueError())
                .build();
    }
}
