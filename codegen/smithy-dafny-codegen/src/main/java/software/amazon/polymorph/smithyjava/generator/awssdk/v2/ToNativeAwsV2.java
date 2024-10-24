// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.awssdk.v2;

import static software.amazon.smithy.utils.StringUtils.capitalize;

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
import software.amazon.polymorph.smithyjava.nameresolver.AwsSdkDafnyV2;
import software.amazon.polymorph.smithyjava.nameresolver.AwsSdkNativeV2;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
import software.amazon.polymorph.utils.DafnyNameResolverHelpers;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
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
 * ToNativeAwsV2 generates ToNative.
 * ToNative is a helper class for the AwsSdk's {@link ShimV2}.<p>
 * ToNative contains methods to convert
 * a subset of an AWS SDK Service's types
 * from Dafny generated Java to native Java.<p>
 * The subset is composed of:
 * <ul>
 *   <li>All the Service's Operations' inputs
 *   <li>All the Service's Operations' outputs
 *   <li>All the Service's Errors
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

  protected static final String VAR_BUILDER = "builder";
  protected static final String VAR_TEMP = "temp";

  // TODO: for V2 support, use abstract AwsSdk name resolvers and sub class for V1 or V2.

  // Hack to override CodegenSubject
  // See code comment on ../library/ModelCodegen for details.
  private final JavaAwsSdkV2 subject;

  public static ClassName className(ShapeId shapeId) {
    if (!AwsSdkNameResolverHelpers.isInAwsSdkNamespace(shapeId)) {
      throw new IllegalArgumentException(
        "ShapeId MUST BE in an AWS SDK Namespace"
      );
    }
    return ClassName.get(
      DafnyNameResolverHelpers.packageNameForNamespace(shapeId.getNamespace()),
      TO_NATIVE
    );
  }

  protected static Map<
    ShapeType,
    MethodReference
  > V2_CONVERSION_METHOD_FROM_SHAPE_TYPE;

  static {
    V2_CONVERSION_METHOD_FROM_SHAPE_TYPE =
      Map.ofEntries(
        Map.entry(
          ShapeType.BLOB,
          new MethodReference(
            JavaAwsSdkV2.BLOB_TO_NATIVE_SDK_BYTES,
            "fromByteArray"
          )
        ),
        Map.entry(
          ShapeType.TIMESTAMP,
          new MethodReference(COMMON_TO_NATIVE_SIMPLE, "Instant")
        )
      );
  }

  public ToNativeAwsV2(JavaAwsSdkV2 awsSdk) {
    super(awsSdk, className(awsSdk.serviceShape.toShapeId()));
    this.subject = awsSdk;
  }

  @Override
  public Set<JavaFile> javaFiles() {
    JavaFile.Builder builder = JavaFile.builder(
      subject.packageName,
      toNative()
    );
    return Collections.singleton(builder.build());
  }

  TypeSpec toNative() {
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

    List<MethodSpec> convertRelevant = allRelevantShapeIds
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
    return TypeSpec
      .classBuilder(ClassName.get(subject.packageName, TO_NATIVE))
      .addModifiers(Modifier.PUBLIC)
      .addMethods(convertRelevant)
      .addMethods(convertServiceErrors)
      .addMethod(modeledService(subject.serviceShape))
      .addMethod(errorOpaque())
      .build();
  }

  /**
   * The Dafny representation of an AWS SDK Service is a
   * Polymorph generated Shim wrapping that Service Client.</p>
   * Thus, the Native equivalent is the wrapped Service Client.</p>
   * i.e.: For KMS, this method generates:</p>
   * <pre>
   * public static KmsClient KeyManagementService(IKeyManagementServiceClient dafnyValue) {
   *   return ((Shim) dafnyValue).impl();
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
      .addParameter(dafnyClass, VAR_INPUT)
      .returns(nativeClass)
      .addStatement("return (($T) $L).impl()", shim, VAR_INPUT)
      .build();
  }

  @SuppressWarnings({ "OptionalGetWithoutIsPresent" })
  MethodSpec generateConvert(ShapeId shapeId) {
    final Shape shape = subject.model
      .getShape(shapeId)
      .orElseThrow(() ->
        new IllegalStateException("Cannot find shape " + shapeId)
      );
    return switch (shape.getType()) {
      // For the AWS SDK for Java V2, we do not generate converters for simple shapes
      case BLOB,
        BOOLEAN,
        TIMESTAMP,
        BYTE,
        SHORT,
        DOUBLE,
        INTEGER,
        LONG,
        BIG_DECIMAL,
        BIG_INTEGER,
        MEMBER -> null;
      case STRING -> generateConvertString(shapeId); // STRING handles enums
      case LIST -> modeledList(shape.asListShape().get());
      case SET -> modeledSet(shape.asSetShape().get());
      case MAP -> modeledMap(shape.asMapShape().get());
      case STRUCTURE -> modeledStructure(shape.asStructureShape().get());
      case UNION -> modeledUnion(shape.asUnionShape().get());
      case ENUM -> generateConvertEnum(shapeId);
      default -> throw new UnsupportedOperationException(
        "ShapeId %s is of Type %s, which is not yet supported for ToNative".formatted(
            shapeId,
            shape.getType()
          )
      );
    };
  }

  @Override
  protected MethodSpec modeledListOrSet(
    MemberShape memberShape,
    ShapeId shapeId,
    ShapeType shapeType
  ) {
    // BinarySetAttributeValue conversion is special.
    // The input Dafny type is DafnySequence<? extends DafnySequence<? extends Byte>>.
    // The output native type is List<SdkBytes>.
    // dafny-java-conversion can convert most input types directly to the output types;
    //     however, SdkBytes is an exception. SdkBytes is defined in the AWS SDK. It is not a
    //     native Java nor Dafny type.
    // We do not want to write a conversion to SdkBytes inside dafny-java-conversion, else
    //     Polymorph would need to take a dependency on the AWS SDK. Instead, smithy-dafny
    //     will generate the required conversion code.
    // This is the only time when Polymorph needs to convert a list of a Dafny type to a list
    //     of a type that Polymorph does not know about. So this is a special case and warrants
    //     its own generation logic.
    if (shapeId.getName().contains("BinarySetAttributeValue")) {
      ParameterSpec parameterSpec = ParameterSpec
        .builder(subject.dafnyNameResolver.typeForShape(shapeId), VAR_INPUT)
        .build();

      MethodSpec.Builder methodSpecBuilder = MethodSpec
        .methodBuilder(capitalize(shapeId.getName()))
        .addModifiers(PUBLIC_STATIC)
        .returns(subject.nativeNameResolver.typeForShape(shapeId))
        .addParameter(parameterSpec);

      // Since this special case only applies to one class right now, explicitly assigning a
      //     string isn't unreasonable. We should extend this logic if this case applies to
      //     more classes as we add new libraries.
      CodeBlock.Builder codeBlockBuilder = CodeBlock.builder();
      codeBlockBuilder.add(
        """
            List<SdkBytes> returnList = new $L<SdkBytes>();

            dafnyValue.forEach((value) -> {
                returnList.add(software.amazon.awssdk.core.SdkBytes.fromByteArray((byte[]) value.toRawArray()));
            });

            return returnList;
        """,
        Constants.JAVA_UTIL_ARRAYLIST
      );

      methodSpecBuilder.addCode(codeBlockBuilder.build());

      return methodSpecBuilder.build();
    }

    return super.modeledListOrSet(memberShape, shapeId, shapeType);
  }

  @Override
  protected MethodSpec modeledStructure(StructureShape structureShape) {
    String methodName = capitalize(structureShape.getId().getName());
    ClassName nativeClassName =
      subject.nativeNameResolver.classNameForStructure(structureShape);
    MethodSpec.Builder builder = MethodSpec
      .methodBuilder(methodName)
      .addModifiers(Modifier.STATIC, Modifier.PUBLIC)
      .returns(nativeClassName)
      .addParameter(
        subject.dafnyNameResolver.typeForShape(structureShape.getId()),
        VAR_INPUT
      );

    if (structureShape.members().size() == 0) {
      builder.addStatement("return $T.builder().build()", nativeClassName);
      return builder.build();
    }
    builder.addStatement(
      "$T.Builder $L = $T.builder()",
      nativeClassName,
      VAR_BUILDER,
      nativeClassName
    );

    // For each member
    structureShape
      .members()
      .stream()
      .sorted()
      .forEach(member -> {
        // if optional, check if present
        if (member.isOptional()) {
          builder.beginControlFlow(
            "if ($L.$L.is_Some())",
            VAR_INPUT,
            Dafny.getMemberField(member)
          );
        }
        // set with conversion call
        builder.addStatement(
          setWithConversionCall(member, Dafny.getMemberFieldValue(member))
        );
        if (member.isOptional()) builder.endControlFlow();
      });
    return builder.addStatement("return $L.build()", VAR_BUILDER).build();
  }

  @Override
  protected CodeBlock setWithConversionCall(
    MemberShape member,
    CodeBlock getMember
  ) {
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
      return CodeBlock.of(
        "$L.$L($L((byte[]) ($L.$L.toRawArray())))",
        VAR_BUILDER,
        setMemberField(member),
        conversionMethodReference(member).asNormalReference(),
        VAR_INPUT,
        AwsSdkDafnyV2.getV2MemberFieldValue(member)
      );
    }

    return CodeBlock.of(
      "$L.$L($L($L.$L))",
      VAR_BUILDER,
      setMemberField(member),
      conversionMethodReference(member).asNormalReference(),
      VAR_INPUT,
      AwsSdkDafnyV2.getV2MemberFieldValue(member)
    );
  }

  protected MethodReference conversionMethodReference(MemberShape memberShape) {
    Shape targetShape = subject.model.expectShape(memberShape.getTarget());
    if (
      V2_CONVERSION_METHOD_FROM_SHAPE_TYPE.containsKey(targetShape.getType())
    ) {
      return V2_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(targetShape.getType());
    }
    return super.conversionMethodReference(targetShape);
  }

  /** @return CodeBlock of Method to set a member field. */
  @Override
  protected CodeBlock setMemberField(MemberShape shape) {
    return subject.nativeNameResolver.fieldForSetMember(shape);
  }

  MethodSpec generateConvertString(ShapeId shapeId) {
    final StringShape shape = subject.model.expectShape(
      shapeId,
      StringShape.class
    );
    if (shape.hasTrait(EnumTrait.class)) {
      return generateConvertEnum(shapeId);
    }
    return null;
  }

  MethodSpec generateConvertEnum(ShapeId shapeId) {
    final StringShape shape = subject.model.expectShape(
      shapeId,
      StringShape.class
    );
    final ClassName returnType = subject.nativeNameResolver.classForEnum(shape);
    MethodSpec method = modeledEnum(shape);
    return method;
  }

  protected final MethodSpec modeledEnum(StringShape shape) {
    final ShapeId shapeId = shape.getId();
    final String methodName = capitalize(shapeId.getName());
    final TypeName inputType = subject.dafnyNameResolver.typeForShape(shapeId);
    final ClassName returnType = subject.nativeNameResolver.classForEnum(shape);
    MethodSpec.Builder method = initializeMethodSpec(
      methodName,
      inputType,
      returnType
    );
    final EnumTrait enumTrait = shape.getTrait(EnumTrait.class).orElseThrow();
    if (!enumTrait.hasNames()) {
      throw new UnsupportedOperationException(
        "Unnamed enums not supported. ShapeId: %s".formatted(shapeId)
      );
    }

    enumTrait
      .getValues()
      .stream()
      .map(EnumDefinition::getName)
      .map(maybeName ->
        maybeName.orElseThrow(() ->
          new IllegalArgumentException(
            "Unnamed enums not supported. ShapeId: %s".formatted(shapeId)
          )
        )
      )
      .peek(name -> {
        if (!ModelUtils.isValidEnumDefinitionName(name)) {
          throw new UnsupportedOperationException(
            "Invalid enum definition name: %s".formatted(name)
          );
        }
      })
      .forEachOrdered(name ->
        method
          .beginControlFlow(
            "if ($L.$L())",
            VAR_INPUT,
            Dafny.datatypeConstructorIs(name)
          )
          .addStatement(
            "return $T.$L",
            returnType,
            subject.nativeNameResolver.v2FormattedEnumValue(shapeId, name)
          )
          .endControlFlow()
      );

    method.addStatement(
      "return $T.fromValue($L.toString())",
      returnType,
      VAR_INPUT
    );
    return method.build();
  }

  // TODO: Refactor with ToNative.
  // This is only duplicated because ToNative uses "nativeBuilder" as the name for its builders,
  //     but this file uses "builder". This seems able to be refactored.
  protected MethodSpec modeledUnion(final UnionShape shape) {
    final ShapeId shapeId = shape.getId();
    final String methodName = capitalize(shapeId.getName());
    final TypeName inputType = subject.dafnyNameResolver.typeForShape(shapeId);
    final ClassName returnType =
      subject.nativeNameResolver.classNameForStructure(shape);
    MethodSpec.Builder method = initializeMethodSpec(
      methodName,
      inputType,
      returnType
    );
    ClassName nativeClassName =
      subject.nativeNameResolver.classNameForStructure(
        shape.asUnionShape().get()
      );
    method.addStatement(
      "$T.Builder $L = $T.builder()",
      nativeClassName,
      VAR_BUILDER,
      nativeClassName
    );
    shape
      .members()
      .forEach(member -> {
        method
          .beginControlFlow(
            "if ($L.$L())",
            VAR_INPUT,
            Dafny.datatypeConstructorIs(member.getMemberName())
          )
          .addStatement(
            setWithConversionCall(member, Dafny.getMemberField(member))
          )
          .endControlFlow();
      });
    method.addStatement("return $L.build()", VAR_BUILDER);
    return method.build();
  }

  protected MethodSpec errorOpaque() {
    final String methodName = "Error";
    final TypeName inputType = subject.dafnyNameResolver.classForOpaqueError();
    final ClassName returnType = ClassName.get(RuntimeException.class);
    return initializeMethodSpec(methodName, inputType, returnType)
      .addComment("While the first two cases are logically identical,")
      .addComment("there is a semantic distinction.")
      .addComment(
        "An un-modeled Service Error is different from a Java Heap Exhaustion error."
      )
      .addComment("In the future, Smithy-Dafny MAY allow for this distinction.")
      .addComment(
        "Which would allow Dafny developers to treat the two differently."
      )
      // If obj is an instance of the Service's Base Exception
      .beginControlFlow(
        "if ($L.$L instanceof $T)",
        VAR_INPUT,
        Dafny.datatypeDeconstructor("obj"),
        subject.nativeNameResolver.baseErrorForService()
      )
      .addStatement(
        "return ($T) $L.$L",
        subject.nativeNameResolver.baseErrorForService(),
        VAR_INPUT,
        Dafny.datatypeDeconstructor("obj")
      )
      // If obj is ANY Exception
      .nextControlFlow(
        "else if ($L.$L instanceof $T)",
        VAR_INPUT,
        Dafny.datatypeDeconstructor("obj"),
        Exception.class
      )
      .addStatement(
        "return ($T) $L.$L",
        RuntimeException.class,
        VAR_INPUT,
        Dafny.datatypeDeconstructor("obj")
      )
      .endControlFlow()
      // If obj is not ANY exception and String is not set, Give Up with IllegalStateException
      .addStatement(
        "return new $T(String.format($S, $L))",
        IllegalStateException.class,
        "Unknown error thrown while calling " +
        AwsSdkNativeV2.titleForService(subject.serviceShape) +
        ". %s",
        VAR_INPUT
      )
      .build();
  }
}
