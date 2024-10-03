// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.awssdk.v2;

import static software.amazon.polymorph.smithyjava.generator.awssdk.v2.JavaAwsSdkV2.SDK_BYTES_AS_BYTE_BUFFER;
import static software.amazon.smithy.utils.StringUtils.capitalize;

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
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import javax.lang.model.element.Modifier;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import software.amazon.polymorph.smithyjava.generator.ToDafny;
import software.amazon.polymorph.smithyjava.nameresolver.AwsSdkDafnyV2;
import software.amazon.polymorph.smithyjava.nameresolver.AwsSdkNativeV2;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
import software.amazon.polymorph.utils.DafnyNameResolverHelpers;
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
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.model.traits.EnumDefinition;
import software.amazon.smithy.model.traits.EnumTrait;

//TODO: Create abstract class for V1 & V2 to extend
/**
 * ToDafnyAwsV2 generates ToDafny.
 * ToDafny is a helper class for the AwsSdk's {@link ShimV2}.<p>
 * It holds methods to convert
 * a subset of an AWS SDK Service's types to Dafny types.<p>
 * The subset is composed of:
 * <ul>
 *   <li>All the Service's Operations' outputs
 *   <li>All the Service's Operations' inputs
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

  private static final Logger LOGGER = LoggerFactory.getLogger(
    ToDafnyAwsV2.class
  );
  // Hack to override subject to JavaAwsSdkV2
  // See code comment on ../library/ModelCodegen for details.
  final JavaAwsSdkV2 subject;

  public static ClassName className(ShapeId shapeId) {
    if (!AwsSdkNameResolverHelpers.isInAwsSdkNamespace(shapeId)) {
      throw new IllegalArgumentException(
        "ShapeId MUST BE in an AWS SDK Namespace"
      );
    }
    return ClassName.get(
      DafnyNameResolverHelpers.packageNameForNamespace(shapeId.getNamespace()),
      TO_DAFNY
    );
  }

  public ToDafnyAwsV2(JavaAwsSdkV2 awsSdk) {
    super(awsSdk, className(awsSdk.serviceShape.toShapeId()));
    this.subject = awsSdk;
  }

  @Override
  public Set<JavaFile> javaFiles() {
    JavaFile.Builder builder = JavaFile.builder(
      subject.dafnyNameResolver.packageName(),
      toDafny()
    );
    return Collections.singleton(builder.build());
  }

  TypeSpec toDafny() {
    List<OperationShape> operations = subject.serviceShape
      .getOperations()
      .stream()
      .sorted()
      .map(shapeId -> subject.model.expectShape(shapeId, OperationShape.class))
      .toList();
    LinkedHashSet<ShapeId> operationStructures = operations
      .stream()
      .map(OperationShape::getInputShape)
      .sorted()
      .collect(Collectors.toCollection(LinkedHashSet::new));
    operations
      .stream()
      .map(OperationShape::getOutputShape)
      .sorted()
      .forEachOrdered(operationStructures::add);
    LinkedHashSet<ShapeId> serviceErrors = ModelUtils
      .streamServiceErrors(subject.model, subject.serviceShape)
      .map(Shape::toShapeId)
      .sorted()
      // InvalidEndpointException does not exist in SDK V2
      .filter(structureShapeId ->
        !structureShapeId
          .toString()
          .contains("com.amazonaws.dynamodb#InvalidEndpointException")
      )
      .collect(Collectors.toCollection(LinkedHashSet::new));

    operationStructures.addAll(serviceErrors);
    Set<ShapeId> allRelevantShapeIds = ModelUtils.findAllDependentShapes(
      operationStructures,
      subject.model
    );
    allRelevantShapeIds.removeAll(serviceErrors);
    allRelevantShapeIds.remove(ShapeId.fromParts("smithy.api", "Unit"));
    // Enums are also a special case
    LinkedHashSet<ShapeId> enumShapeIds = new LinkedHashSet<>();
    allRelevantShapeIds.forEach(shapeId -> {
      Shape shape = subject.model.expectShape(shapeId);
      if (shape.hasTrait(EnumTrait.class)) {
        enumShapeIds.add(shapeId);
      }
    });
    allRelevantShapeIds.removeAll(enumShapeIds);

    final List<MethodSpec> convertAllRelevant = allRelevantShapeIds
      .stream()
      .sorted()
      .map(this::generateConvert)
      .filter(Objects::nonNull)
      .toList();
    final List<MethodSpec> convertServiceErrors = serviceErrors
      .stream()
      .sorted()
      .map(this::modeledError)
      .toList();
    // For enums, we generate overloaded methods,
    // one to convert instances of the Enum
    final List<MethodSpec> convertEnumEnum = enumShapeIds
      .stream()
      .sorted()
      .map(this::generateConvertEnumEnum)
      .toList();
    // The other to convert String representatives of the enum
    final List<MethodSpec> convertEnumString = enumShapeIds
      .stream()
      .sorted()
      .map(this::generateConvertEnumString)
      .toList();

    return TypeSpec
      .classBuilder(
        ClassName.get(subject.dafnyNameResolver.packageName(), "ToDafny")
      )
      .addModifiers(Modifier.PUBLIC)
      .addMethods(convertAllRelevant)
      .addMethods(convertServiceErrors)
      .addMethods(convertEnumEnum)
      .addMethods(convertEnumString)
      .addMethod(generateConvertOpaqueServiceError())
      .addMethod(generateConvertOpaqueError())
      .addMethod(modeledService(subject.serviceShape))
      .build();
  }

  /**
   * The Dafny representation of an AWS SDK Service is a
   * Polymorph generated Shim wrapping that Service Client.</p>
   * i.e.: For KMS, this method generates:</p>
   * <pre>
   * public static IKeyManagementServiceClient KeyManagementService(KmsClient nativeValue) {
   *   return new Shim(nativeValue, null);
   * }
   * </pre>
   */
  MethodSpec modeledService(ServiceShape shape) {
    String methodName = capitalize(shape.toShapeId().getName());
    ClassName nativeClass = AwsSdkNativeV2.classNameForServiceClient(shape);
    ClassName dafnyClass = AwsSdkDafnyV2.classNameForAwsService(shape);
    ClassName shim = ShimV2.className(shape);
    return MethodSpec
      .methodBuilder(methodName)
      .addModifiers(PUBLIC_STATIC)
      .addParameter(nativeClass, VAR_INPUT)
      .returns(dafnyClass)
      .addStatement("return new $T($L, null)", shim, VAR_INPUT)
      .build();
  }

  /** This method:
   * 1. Determines the Shape Type
   * 2. invokes the correct generate for that shape type
   */
  @SuppressWarnings({ "OptionalGetWithoutIsPresent", "DuplicatedCode" })
  MethodSpec generateConvert(final ShapeId shapeId) {
    final Shape shape = subject.model
      .getShape(shapeId)
      .orElseThrow(() ->
        new IllegalStateException("Cannot find shape " + shapeId)
      );
    return switch (shape.getType()) {
      // For the AWS SDK for Java, we do not generate converters for simple shapes
      case BLOB,
        BOOLEAN,
        STRING,
        TIMESTAMP,
        BYTE,
        SHORT,
        DOUBLE,
        INTEGER,
        LONG,
        BIG_DECIMAL,
        BIG_INTEGER,
        MEMBER -> null;
      case LIST -> modeledList(shape.asListShape().get());
      case MAP -> modeledMap(shape.asMapShape().get());
      case SET -> modeledSet(shape.asSetShape().get());
      case STRUCTURE -> generateConvertStructure(shapeId);
      case UNION -> generateConvertUnion(shapeId);
      default -> throw new UnsupportedOperationException(
        "ShapeId %s is of Type %s, which is not yet supported for ToDafny".formatted(
            shapeId,
            shape.getType()
          )
      );
    };
  }

  MethodSpec generateConvertUnion(final ShapeId shapeId) {
    final UnionShape unionShape = subject.model.expectShape(
      shapeId,
      UnionShape.class
    );
    if (shapeId.toString().equals("com.amazonaws.dynamodb#AttributeValue")) {
      return ddbAttributeValueConversion(shapeId, unionShape);
    }
    LOGGER.warn(
      "Encountered an AWS SDK Union Shape!" +
      "Historically, we have not been good at generating these!\n" +
      "Union ShapeID: %s".formatted(shapeId)
    );
    return super.modeledUnion(unionShape);
  }

  /** */
  private MethodSpec ddbAttributeValueConversion(
    final ShapeId shapeId,
    final UnionShape shape
  ) {
    String methodName = capitalize(shapeId.getName());
    TypeName returnType = subject.dafnyNameResolver.typeForShape(shapeId);
    MethodSpec.Builder method = MethodSpec
      .methodBuilder(methodName)
      .addModifiers(PUBLIC_STATIC)
      .returns(returnType)
      .addParameter(
        subject.nativeNameResolver.classNameForStructure(shape),
        VAR_INPUT
      );
    method.beginControlFlow("switch ($L.type())", VAR_INPUT);
    shape
      .members()
      .forEach(member -> {
        CodeBlock getField = getMember(
          CodeBlock.builder().add(VAR_INPUT).build(),
          member
        );
        CodeBlock memberConversion = memberConversion(member, getField);
        String datatypeConstructorCreate = Dafny.datatypeConstructorCreate(
          member.getMemberName(),
          false
        );
        // The DDB Model uses NULL, but AWS SDK V2 uses NUL
        String memberName = member.getMemberName().equals("NULL")
          ? "NUL"
          : member.getMemberName();
        method
          .beginControlFlow("case $L:", memberName)
          .addStatement(
            "return $T.$L($L)",
            returnType,
            datatypeConstructorCreate,
            memberConversion
          )
          .endControlFlow();
      });
    method
      .beginControlFlow("default:")
      .addStatement(
        "throw new $T($S + $L + $S)",
        IllegalArgumentException.class,
        "Cannot convert ",
        VAR_INPUT,
        " to %s.".formatted(returnType)
      )
      .endControlFlow();
    method.endControlFlow();
    return method.build();
  }

  @Override
  protected CodeBlock memberConversion(
    MemberShape memberShape,
    CodeBlock inputVar
  ) {
    CodeBlock methodBlock = conversionMethodReference(
      subject.model.expectShape(memberShape.getTarget())
    )
      .asNormalReference();

    return CodeBlock.of(
      "$L($L)",
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
  public CodeBlock formatInputVarForMemberConversion(
    MemberShape memberShape,
    CodeBlock inputVar
  ) {
    CodeBlock.Builder returnCodeBlockBuilder = CodeBlock
      .builder()
      .add(inputVar);

    // If methodBlock is transforming to Dafny ByteSequence, it is expecting either a byte[]
    //   or ByteBuffer.
    // In this case, inputVar is of type SdkBytes.
    // dafny-java-conversion should not have a ByteSequence constructor that directly takes in
    //   SdkBytes. If it did, Polymorph would need to depend on AWS SDK for Java V2.
    // The conversion from inputVar as SdkBytes to a Dafny ByteSequence looks like
    //   ByteSequence(inputVar.asByteArray())
    Shape targetShape = subject.model.expectShape(memberShape.getTarget());
    if (targetShape.getType() == ShapeType.BLOB) {
      return returnCodeBlockBuilder.add(".asByteArray()").build();
    }

    // BinarySetAttributeValue conversion is special.
    // The input Dafny type is DafnySequence<? extends DafnySequence<? extends Byte>>.
    // The output native type is List<SdkBytes>.
    // dafny-java-conversion can convert most input types directly to the output types;
    //     however, SdkBytes is an exception. SdkBytes is defined in the AWS SDK. It is not a
    //     native Java nor Dafny type.
    // We do not want to write a conversion to SdkBytes inside dafny-java-conversion, else
    //     Polymorph would need to take a dependency on the AWS SDK. Instead, smithy-dafny-codegen-cli=
    //     will generate the required conversion code.
    // This is the only time when Polymorph needs to convert a list of a Dafny type to a list
    //     of a type that Polymorph does not know about. So this is a special case and warrants
    //     its own generation logic.
    if (
      targetShape
        .getId()
        .toString()
        .equals("com.amazonaws.dynamodb#BinarySetAttributeValue")
    ) {
      return returnCodeBlockBuilder
        .add(
          ".stream()\n.map($L)\n.collect($L.toList())",
          SDK_BYTES_AS_BYTE_BUFFER.asFunctionalReference(),
          Constants.JAVA_UTIL_STREAM_COLLECTORS
        )
        .build();
    }
    return inputVar;
  }

  MethodSpec generateConvertEnumString(ShapeId shapeId) {
    final StringShape shape = subject.model.expectShape(
      shapeId,
      StringShape.class
    );
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
    final StringShape shape = subject.model.expectShape(
      shapeId,
      StringShape.class
    );
    return modeledEnum(shape);
  }

  // TODO: We should make all name resolvers support `formatEnumCaseName`,
  // rather than entirely ignoring the abstract implementation.
  /**
   * This logic is the same as ToDafny's logic,
   * except it calls an only-defined-in-V2 formatEnumCaseName function.
   */
  @Override
  @SuppressWarnings("OptionalGetWithoutIsPresent")
  protected MethodSpec modeledEnum(Shape shape) {
    final ShapeId shapeId = shape.getId();
    String methodName = capitalize(shapeId.getName());
    final EnumTrait enumTrait = shape
      .getTrait(EnumTrait.class)
      .orElseThrow(() ->
        new IllegalArgumentException(
          "Shape must have the enum trait. ShapeId: %s".formatted(shapeId)
        )
      );
    if (!enumTrait.hasNames()) {
      throw new UnsupportedOperationException(
        "Unnamed enums not supported. ShapeId: %s".formatted(shapeId)
      );
    }
    TypeName dafnyEnumClass = subject.dafnyNameResolver.typeForShape(shapeId);

    MethodSpec.Builder builder = MethodSpec
      .methodBuilder(methodName)
      .addModifiers(Modifier.STATIC, Modifier.PUBLIC)
      .returns(dafnyEnumClass)
      .addParameter(subject.nativeNameResolver.classForEnum(shape), VAR_INPUT)
      .beginControlFlow("switch ($L)", VAR_INPUT);

    final boolean isRecordType = enumTrait.getValues().size() == 1;

    enumTrait
      .getValues()
      .stream()
      .map(EnumDefinition::getName)
      .map(Optional::get)
      .peek(name -> {
        if (!ModelUtils.isValidEnumDefinitionName(name)) {
          throw new UnsupportedOperationException(
            "Invalid enum definition name: %s".formatted(name)
          );
        }
      })
      .forEach(name ->
        builder
          .beginControlFlow(
            "case $L:",
            subject.dafnyNameResolver.formatEnumCaseName(dafnyEnumClass, name)
          )
          .addStatement(
            "return $T.$L()",
            dafnyEnumClass,
            Dafny.datatypeConstructorCreate(name, isRecordType)
          )
          .endControlFlow()
      );

    builder
      .beginControlFlow("default:")
      .addStatement(
        "throw new $T($S + $L + $S)",
        RuntimeException.class,
        "Cannot convert ",
        VAR_INPUT,
        " to %s.".formatted(dafnyEnumClass)
      )
      .endControlFlow();
    builder.endControlFlow();
    return builder.build();
  }

  MethodSpec generateConvertStructure(final ShapeId shapeId) {
    final StructureShape structureShape = subject.model.expectShape(
      shapeId,
      StructureShape.class
    );
    return super.modeledStructure(structureShape);
  }

  @Override
  protected CodeBlock getMember(
    CodeBlock variableName,
    MemberShape memberShape
  ) {
    return subject.dafnyNameResolver.methodForGetMember(
      variableName,
      memberShape
    );
  }

  /**
   * We have to customize
   * List conversion for the AWS SDK for Java V2 because
   * AWS SDK Java V2 treats Enums in a special way.
   * See the comment on
   * {@link AwsSdkNativeV2#typeForShapeNoEnum}
   **/
  @Override
  protected MethodSpec modeledList(ListShape shape) {
    MemberShape memberShape = shape.getMember();
    CodeBlock memberConverter = conversionMethodReference(
      subject.model.expectShape(memberShape.getTarget())
    )
      .asFunctionalReference();
    CodeBlock genericCall = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE
      .get(shape.getType())
      .asNormalReference();
    CodeBlock getTypeDescriptor = subject.dafnyNameResolver.typeDescriptor(
      memberShape.getTarget()
    );

    ParameterSpec parameterSpec = ParameterSpec
      .builder(
        subject.nativeNameResolver.typeForListSetOrMapNoEnum(shape.getId()),
        "nativeValue"
      )
      .build();

    MethodSpec.Builder methodSpecBuilder = MethodSpec
      .methodBuilder(capitalize(shape.getId().getName()))
      .addModifiers(Modifier.PUBLIC, Modifier.STATIC)
      .returns(
        subject.dafnyNameResolver.typeForAggregateWithWildcard(shape.getId())
      )
      .addParameter(parameterSpec);

    // A static call to TypeDescriptor class requires an explicit typecast.
    // This generates an "unchecked cast" warning, which needs to be suppressed.
    // (Dafny automatically generates this warning suppression annotation for classes that
    //     generate their own _typeDescriptor() method.)
    if (
      subject.dafnyNameResolver.shapeIdRequiresStaticTypeDescriptor(
        memberShape.getTarget()
      )
    ) {
      return methodSpecBuilder
        // Suppress "unchecked cast" warning; this is expected
        .addAnnotation(
          AnnotationSpec
            .builder(SuppressWarnings.class)
            .addMember("value", "$S", "unchecked")
            .build()
        )
        .addStatement(
          "return \n($L) \n$L(\n$L, \n$L, \n$L)",
          // This is the explicit typecast in the return statement
          subject.dafnyNameResolver.typeForAggregateWithWildcard(shape.getId()),
          genericCall,
          "nativeValue",
          memberConverter,
          getTypeDescriptor
        )
        .build();
    }

    return methodSpecBuilder
      .addStatement(
        "return $L(\n$L, \n$L, \n$L)",
        genericCall,
        "nativeValue",
        memberConverter,
        getTypeDescriptor
      )
      .build();
  }

  /**
   * We have to customize
   * Set conversion for the AWS SDK for Java V2 because
   * AWS SDK Java V2 treats Enums in a special way.
   * See the comment on
   * {@link AwsSdkNativeV2#typeForShapeNoEnum}
   **/
  @Override
  protected MethodSpec modeledSet(SetShape shape) {
    MemberShape memberShape = shape.getMember();
    CodeBlock memberConverter = conversionMethodReference(
      subject.model.expectShape(memberShape.getTarget())
    )
      .asFunctionalReference();
    CodeBlock genericCall = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE
      .get(shape.getType())
      .asNormalReference();
    ParameterSpec parameterSpec = ParameterSpec
      .builder(
        subject.nativeNameResolver.typeForListSetOrMapNoEnum(shape.getId()),
        "nativeValue"
      )
      .build();
    return MethodSpec
      .methodBuilder(capitalize(shape.getId().getName()))
      .addModifiers(Modifier.PUBLIC, Modifier.STATIC)
      .returns(
        subject.dafnyNameResolver.typeForAggregateWithWildcard(shape.getId())
      )
      .addParameter(parameterSpec)
      .addStatement(
        "return $L(\nnativeValue, \n$L)",
        genericCall,
        memberConverter
      )
      .build();
  }

  /**
   * We have to customize
   * Map conversion for the AWS SDK for Java V2 because
   * AWS SDK Java V2 treats Enums in a special way.
   * See the comment on
   * {@link AwsSdkNativeV2#typeForShapeNoEnum}
   **/
  @Override
  @SuppressWarnings("OptionalGetWithoutIsPresent")
  protected MethodSpec modeledMap(MapShape shape) {
    MemberShape keyShape = shape.getKey().asMemberShape().get();
    CodeBlock keyConverter = conversionMethodReference(
      subject.model.expectShape(keyShape.getTarget())
    )
      .asFunctionalReference();
    MemberShape valueShape = shape.getValue().asMemberShape().get();
    CodeBlock valueConverter = conversionMethodReference(
      subject.model.expectShape(valueShape.getTarget())
    )
      .asFunctionalReference();
    CodeBlock genericCall = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE
      .get(shape.getType())
      .asNormalReference();
    ParameterSpec parameterSpec = ParameterSpec
      .builder(
        subject.nativeNameResolver.typeForListSetOrMapNoEnum(shape.getId()),
        "nativeValue"
      )
      .build();
    return MethodSpec
      .methodBuilder(capitalize(shape.getId().getName()))
      .addModifiers(Modifier.PUBLIC, Modifier.STATIC)
      .returns(
        subject.dafnyNameResolver.typeForAggregateWithWildcard(shape.getId())
      )
      .addParameter(parameterSpec)
      .addStatement(
        "return $L(\nnativeValue, \n$L, \n$L)",
        genericCall,
        keyConverter,
        valueConverter
      )
      .build();
  }

  MethodSpec generateConvertOpaqueServiceError() {
    // Opaque Errors are not in the model,
    // so we cannot use any of our helper methods for this method.
    return MethodSpec
      .methodBuilder("Error")
      .addModifiers(Modifier.PUBLIC, Modifier.STATIC)
      .returns(subject.dafnyNameResolver.abstractClassForError())
      .addComment(
        "While this is logically identical to the other Opaque Error case,"
      )
      .addComment("it is semantically distinct.")
      .addComment(
        "An un-modeled Service Error is different from a Java Heap Exhaustion error."
      )
      .addComment("In the future, Smithy-Dafny MAY allow for this distinction.")
      .addComment(
        "Which would allow Dafny developers to treat the two differently."
      )
      .addParameter(
        subject.nativeNameResolver.baseErrorForService(),
        "nativeValue"
      )
      .addStatement(
        "return $T.create_Opaque(nativeValue, dafny.DafnySequence.asString(nativeValue.getMessage()))",
        subject.dafnyNameResolver.abstractClassForError()
      )
      .build();
  }

  MethodSpec generateConvertOpaqueError() {
    // Opaque Errors are not in the model,
    // so we cannot use any of our helper methods for this method.
    return MethodSpec
      .methodBuilder("Error")
      .addModifiers(Modifier.PUBLIC, Modifier.STATIC)
      .returns(subject.dafnyNameResolver.abstractClassForError())
      .addParameter(Exception.class, "nativeValue")
      .addComment(
        "While this is logically identical to the other Opaque Error case,"
      )
      .addComment("it is semantically distinct.")
      .addComment(
        "An un-modeled Service Error is different from a Java Heap Exhaustion error."
      )
      .addComment("In the future, Smithy-Dafny MAY allow for this distinction.")
      .addComment(
        "Which would allow Dafny developers to treat the two differently."
      )
      .addStatement(
        "return $T.create_Opaque(nativeValue, dafny.DafnySequence.asString(nativeValue.getMessage()))",
        subject.dafnyNameResolver.abstractClassForError()
      )
      .build();
  }
}
