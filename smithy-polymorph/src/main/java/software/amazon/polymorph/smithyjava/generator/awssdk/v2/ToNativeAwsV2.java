package software.amazon.polymorph.smithyjava.generator.awssdk.v2;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.JavaFile;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.ParameterSpec;
import com.squareup.javapoet.TypeName;
import com.squareup.javapoet.TypeSpec;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.stream.Collectors;

import javax.lang.model.element.Modifier;

import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.polymorph.smithyjava.generator.ToNative;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.utils.ModelUtils;

import software.amazon.smithy.model.shapes.ListShape;
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

import static software.amazon.polymorph.smithyjava.generator.Generator.Constants.JAVA_UTIL_ARRAYLIST;
import static software.amazon.smithy.utils.StringUtils.capitalize;
import static software.amazon.smithy.utils.StringUtils.uncapitalize;

/**
 * ToNativeAwsV2 generates ToNative.
 * ToNative is a helper class for the AwsSdk's {@link ShimV2}.<p>
 * ToNative contains methods to convert
 * a subset of an AWS SDK Service's types
 * from Dafny generated Java to native Java.<p>
 * The subset is composed of:
 * <ul>
 *   <li>All the Service's Operations' inputs
 *   <li>All the fields contained by the above
 * </ul>
 * As such,
 * ToNativeAwsV2 holds the logic to generate these methods based on:
 * <ul>
 *     <li>a smithy model</li>
 *     <li>knowledge of how smithy-dafny generates Dafny for AWS SDK</li>
 *     <li>knowledge of how Dafny compiles Java</li>
 *     <li>knowledge of the patterns of the AWS SDK V2 for Java</li>
 * </ul>
 */
public class ToNativeAwsV2 extends ToNative {
    protected final static String VAR_BUILDER = "builder";
    protected final static String VAR_TEMP = "temp";
    // TODO move
    public static final ClassName BLOB_TO_NATIVE_SDK_BYTES = ClassName.get("software.amazon.awssdk.core", "SdkBytes");

    // TODO: for V2 support, use abstract AwsSdk name resolvers and sub class for V1 or V2.

    // Hack to override CodegenSubject
    // See code comment on ../library/ModelCodegen for details.
    private final JavaAwsSdkV2 subject;

    protected static Map<ShapeType, MethodReference> V2_CONVERSION_METHOD_FROM_SHAPE_TYPE;

    static {
        V2_CONVERSION_METHOD_FROM_SHAPE_TYPE = Map.ofEntries(
            Map.entry(ShapeType.BLOB,
                new MethodReference(BLOB_TO_NATIVE_SDK_BYTES, "fromByteArray")),
            Map.entry(ShapeType.TIMESTAMP,
                new MethodReference(COMMON_TO_NATIVE_SIMPLE, "Instant"))
        );
    }

    public ToNativeAwsV2(JavaAwsSdkV2 awsSdk) {
        super(awsSdk, ClassName.get(awsSdk.packageName, TO_NATIVE));
        this.subject = awsSdk;
    }

    @Override
    public Set<JavaFile> javaFiles() {
        JavaFile.Builder builder = JavaFile.builder(subject.packageName, toNative());
        return Collections.singleton(builder.build());
    }

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
                        ClassName.get(subject.packageName, TO_NATIVE))
                .addModifiers(Modifier.PUBLIC)
                .addMethods(convertRelevant)
                .build();
    }

    @SuppressWarnings({"OptionalGetWithoutIsPresent"})
    MethodSpec generateConvert(ShapeId shapeId) {
        final Shape shape = subject.model.getShape(shapeId)
                .orElseThrow(() -> new IllegalStateException("Cannot find shape " + shapeId));
        return switch (shape.getType()) {
            // For the AWS SDK for Java V2, we do not generate converters for simple shapes
            case BLOB, BOOLEAN, TIMESTAMP, BYTE, SHORT,
                    INTEGER, LONG, BIG_DECIMAL, BIG_INTEGER, MEMBER -> null;
            case STRING -> generateConvertString(shapeId); // STRING handles enums
            case LIST -> modeledList(shape.asListShape().get());
            case SET -> modeledSet(shape.asSetShape().get());
            case MAP -> modeledMap(shape.asMapShape().get());
            case STRUCTURE -> modeledStructure(shape.asStructureShape().get());
            case UNION -> modeledUnion(shape.asUnionShape().get());
            default -> null;
        };
    }

    @Override
    protected MethodSpec modeledListOrSet(MemberShape memberShape, ShapeId shapeId, ShapeType shapeType) {
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
        if (shapeId.getName().contains("BinarySetAttributeValue")) {

            CodeBlock memberConverter = memberConversionMethodReference(memberShape).asFunctionalReference();
            CodeBlock genericCall = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(shapeType).asNormalReference();
            ParameterSpec parameterSpec = ParameterSpec
                .builder(subject.dafnyNameResolver.typeForShape(shapeId), VAR_INPUT)
                .build();

           // System.out.println(subject.nativeNameResolver.typeForShape(shapeId));

            MethodSpec.Builder methodSpecBuilder = MethodSpec
                .methodBuilder(capitalize(shapeId.getName()))
                .addModifiers(PUBLIC_STATIC)
                .returns(subject.nativeNameResolver.typeForShape(shapeId))
                .addParameter(parameterSpec);


            CodeBlock.Builder codeBlockBuilder = CodeBlock.builder();
            codeBlockBuilder.add("""
                List<SdkBytes> returnList = new $L<SdkBytes>();
            
                dafnyValue.forEach((value) -> {
                    returnList.add(software.amazon.awssdk.core.SdkBytes.fromByteArray((byte[]) value.toRawArray()));
                });
            
                return returnList;
            """, JAVA_UTIL_ARRAYLIST);

            methodSpecBuilder.addCode(codeBlockBuilder.build());

            return methodSpecBuilder.build();
        }

        // else call super
        return super.modeledListOrSet(memberShape, shapeId, shapeType);
    }

    @Override
    protected MethodSpec modeledStructure(StructureShape structureShape) {
        String methodName = capitalize(structureShape.getId().getName());
        ClassName nativeClassName = subject.nativeNameResolver.classNameForStructure(structureShape);
        MethodSpec.Builder builder = MethodSpec
                .methodBuilder(methodName)
                .addModifiers(Modifier.STATIC, Modifier.PUBLIC)
                .returns(nativeClassName)
                .addParameter(subject.dafnyNameResolver.typeForShape(structureShape.getId()), VAR_INPUT);

        if (structureShape.members().size() == 0) {
            builder.addStatement("return $T.builder().build()", nativeClassName);
            return builder.build();
        }
        builder.addStatement("$T.Builder $L = $T.builder()", nativeClassName, VAR_BUILDER, nativeClassName);

        // For each member
        structureShape.members()
                .forEach(member -> {
                    // if optional, check if present
                    if (member.isOptional()) {
                        builder.beginControlFlow("if ($L.$L.is_Some())", VAR_INPUT, Dafny.getMemberField(member));
                    }
                    // set with conversion call
                    builder.addStatement(setWithConversionCall(member, Dafny.getMemberFieldValue(member)));
                    if (member.isOptional()) builder.endControlFlow();
                });
        return builder.addStatement("return $L.build()", VAR_BUILDER).build();
    }

    @Override
    protected CodeBlock setWithConversionCall(MemberShape member, CodeBlock getMember) {
        Shape targetShape = subject.model.expectShape(member.getTarget());
        // SDK V2 reads in Blob shapes as SdkBytes.
        // SdkBytes are a Java SDK V2-specific datatype defined in the SDK V2 package. As a result,
        //   dafny-java-version should not define a byte-array-to-SdkBytes conversion. Otherwise,
        //   Polymorph would need to depend on AWS SDK for Java V2.
        // SDK V1 uses ByteBuffers, which are a common Java type defined externally from SDK V1, so
        //   dafny-java-conversion may define a conversion without declaring a dependency on SDK V1.
        // This block converts the Dafny array to a byte array, which is converted to SdkBytes via
        //   SdkBytes.fromByteArray().
        if (targetShape.getType() == ShapeType.BLOB) {
            return CodeBlock.of("$L.$L($L((byte[]) ($L.$L.toRawArray())))",
                VAR_BUILDER,
                setMemberField(member),
                memberConversionMethodReference(member).asNormalReference(),
                VAR_INPUT,
                Dafny.getMemberFieldValue(member));
        }
        // TODO bad, refactor
        // "targetValue" should refer to auto-scaled read/write capacity target values
        if (setMemberField(member).toString().equals("targetValue")) {
            return CodeBlock.of("$L.$L($L((double) $L.$L))",
                VAR_BUILDER,
                setMemberField(member),
                memberConversionMethodReference(member).asNormalReference(),
                VAR_INPUT,
                Dafny.getMemberFieldValue(member));
        }
        return CodeBlock.of("$L.$L($L($L.$L))",
            VAR_BUILDER,
                setMemberField(member),
                memberConversionMethodReference(member).asNormalReference(),
                VAR_INPUT,
                Dafny.getMemberFieldValue(member));
    }

    @Override
    protected MethodReference memberConversionMethodReference(MemberShape memberShape) {
        Shape targetShape = subject.model.expectShape(memberShape.getTarget());
        if (V2_CONVERSION_METHOD_FROM_SHAPE_TYPE.containsKey(targetShape.getType())) {
            return V2_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(targetShape.getType());
        }
        return super.memberConversionMethodReference(memberShape);
    }

    /** @return CodeBlock of Method to set a member field. */
    @Override
    protected CodeBlock setMemberField(MemberShape shape) {
        // In AWS SDK Java V2, using `with` allows for enums or strings
        // while `set` only allows for strings.
        // TODO: Refactor with SSE renaming logic in AwsSdkDafnyV2
        if (shape.getMemberName().contains("SSE")) {
            return CodeBlock.of("$L", shape.getMemberName().replace("SSE", "sse"));
        }
        // TODO: Refactor with KMS renaming logic in AwsSdkDafnyV2
        if (shape.getMemberName().contains("KMS")) {
            return CodeBlock.of("$L", shape.getMemberName().replace("KMS", "kms"));
        }

        // TODO: refactor
        if (isAttributeValueType(shape)) {
            if (shape.getMemberName().equals("NULL")) {
                return CodeBlock.of("nul");
            }
            return CodeBlock.of("$L", shape.getMemberName().toLowerCase());
        }


        return CodeBlock.of("$L", uncapitalize(shape.getMemberName()));
    }

    // TODO refactor
    protected static boolean isAttributeValueType(MemberShape shape) {
        String memberName = shape.getMemberName();
        return memberName.equals("BOOL")
            || memberName.equals("NULL")
            || memberName.equals("L")
            || memberName.equals("M")
            || memberName.equals("BS")
            || memberName.equals("NS")
            || memberName.equals("SS")
            || memberName.equals("B")
            || memberName.equals("N")
            || memberName.equals("S");
    }

    MethodSpec generateConvertString(ShapeId shapeId) {
        final StringShape shape = subject.model.expectShape(shapeId, StringShape.class);
        if (shape.hasTrait(EnumTrait.class)) {
            return generateConvertEnum(shapeId);
        }
        return null;
    }

    MethodSpec generateConvertEnum(ShapeId shapeId) {
        final StringShape shape = subject.model.expectShape(shapeId, StringShape.class);
        final ClassName returnType = subject.nativeNameResolver.classForEnum(shape);
        MethodSpec method = modeledEnum(shape);
        return method;
    }

    protected final MethodSpec modeledEnum(StringShape shape) {
        final ShapeId shapeId = shape.getId();
        final String methodName = capitalize(shapeId.getName());
        final TypeName inputType = subject.dafnyNameResolver.typeForShape(shapeId);
        final ClassName returnType = subject.nativeNameResolver.classForEnum(shape);
        MethodSpec.Builder method = initializeMethodSpec(methodName, inputType, returnType);
        final EnumTrait enumTrait = shape.getTrait(EnumTrait.class).orElseThrow();
        if (!enumTrait.hasNames()) {
            throw new UnsupportedOperationException(
                "Unnamed enums not supported. ShapeId: %s".formatted(shapeId));
        }

        enumTrait.getValues().stream().sequential()
            .map(EnumDefinition::getName)
            .map(maybeName -> maybeName.orElseThrow(
                () -> new IllegalArgumentException(
                    "Unnamed enums not supported. ShapeId: %s".formatted(shapeId))
            ))
            .peek(name -> {
                if (!ModelUtils.isValidEnumDefinitionName(name)) {
                    throw new UnsupportedOperationException(
                        "Invalid enum definition name: %s".formatted(name));
                }
            })
            .forEachOrdered(name -> method
                .beginControlFlow("if ($L.$L())", VAR_INPUT, Dafny.datatypeConstructorIs(name))
                .addStatement("return $T.$L", returnType, subject.nativeNameResolver.v2FormattedEnumValue(returnType, name))
                .endControlFlow()
            );

        method.addStatement("return $T.fromValue($L.toString())", returnType, VAR_INPUT);
        return method.build();
    }

    // TODO: This is duplicated because ToNative uses "nativeBuilder" as builder but this file uses
    // "builder". Fix this
    protected MethodSpec modeledUnion(final UnionShape shape) {
        final ShapeId shapeId = shape.getId();
        final String methodName = capitalize(shapeId.getName());
        final TypeName inputType = subject.dafnyNameResolver.typeForShape(shapeId);
        final ClassName returnType = subject.nativeNameResolver.classNameForStructure(shape);
        MethodSpec.Builder method = initializeMethodSpec(methodName, inputType, returnType);
        // TODO: next 2 lines need to be cleaned up
        ClassName nativeClassName = subject.nativeNameResolver.classNameForStructure(shape.asUnionShape().get());
        method.addStatement("$T.Builder $L = $T.builder()", nativeClassName, VAR_BUILDER, nativeClassName);
        shape.members()
            .forEach(member -> {
                method.beginControlFlow("if ($L.$L())", VAR_INPUT, Dafny.datatypeConstructorIs(member.getMemberName()))
                    .addStatement(setWithConversionCall(member, Dafny.getMemberField(member)))
                    .endControlFlow();
            });
        // TODO: next 2 lines need to be cleaned up
        method.addStatement("return $L.build()", VAR_BUILDER);
        return method.build();
    }

}
