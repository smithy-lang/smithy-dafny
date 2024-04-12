// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator.awssdk.v1;

import static software.amazon.smithy.utils.StringUtils.capitalize;

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
import java.util.Set;
import java.util.stream.Collectors;
import javax.lang.model.element.Modifier;
import software.amazon.polymorph.smithyjava.generator.ToDafny;
import software.amazon.polymorph.smithyjava.nameresolver.AwsSdkDafnyV1;
import software.amazon.polymorph.smithyjava.nameresolver.AwsSdkNativeV1;
import software.amazon.polymorph.smithyjava.nameresolver.Constants;
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
import software.amazon.smithy.model.traits.EnumTrait;

//TODO: Create abstract class for V1 & V2 to extend
/**
 * ToDafnyAwsV1 generates ToDafny.
 * ToDafny is a helper class for the AwsSdk's {@link ShimV1}.<p>
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
 * ToDafnyAwsV1 holds the logic to generate these methods based on:
 * <ul>
 *     <li>a smithy model</li>
 *     <li>knowledge of how smithy-dafny generates Dafny for AWS SDK</li>
 *     <li>knowledge of how Dafny compiles Java</li>
 *     <li>knowledge of the patterns of the AWS SDK V1 for Java</li>
 * </ul>
 */
public class ToDafnyAwsV1 extends ToDafny {

  // Hack to override subject to JavaAwsSdkV1
  // See code comment on ../library/ModelCodegen for details.
  final JavaAwsSdkV1 subject;

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

  public ToDafnyAwsV1(JavaAwsSdkV1 awsSdk) {
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
    LinkedHashSet<ShapeId> operationOutputs = operations
      .stream()
      .map(OperationShape::getOutputShape)
      .sorted()
      .collect(Collectors.toCollection(LinkedHashSet::new));
    LinkedHashSet<ShapeId> operationInputs = operations
      .stream()
      .map(OperationShape::getInputShape)
      .sorted()
      .collect(Collectors.toCollection(LinkedHashSet::new));
    LinkedHashSet<ShapeId> serviceErrors = operations
      .stream()
      .map(OperationShape::getErrors)
      .flatMap(Collection::stream)
      .sorted()
      .collect(Collectors.toCollection(LinkedHashSet::new));
    ModelUtils
      .streamServiceErrors(subject.model, subject.serviceShape)
      .map(Shape::toShapeId)
      .sorted()
      .forEachOrdered(serviceErrors::add);

    LinkedHashSet<ShapeId> operationStructures = new LinkedHashSet<>();
    operationStructures.addAll(operationOutputs);
    operationStructures.addAll(operationInputs);
    operationStructures.addAll(serviceErrors);
    Set<ShapeId> allRelevantShapeIds = ModelUtils.findAllDependentShapes(
      operationStructures,
      subject.model
    );

    // In the AWS SDK for Java V1, Operation Outputs are special
    allRelevantShapeIds.removeAll(operationOutputs);
    // Errors are special case for all generators
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

    final List<MethodSpec> convertOutputs = operationOutputs
      .stream()
      .map(this::generateConvertResponseV1)
      .toList();
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
      .collect(Collectors.toList());
    convertServiceErrors.add(generateConvertOpaqueError());
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
      .classBuilder(className(subject.serviceShape.toShapeId()))
      .addModifiers(Modifier.PUBLIC)
      .addMethods(convertOutputs)
      .addMethods(convertAllRelevant)
      .addMethods(convertServiceErrors)
      .addMethods(convertEnumEnum)
      .addMethods(convertEnumString)
      .addMethod(modeledService(subject.serviceShape))
      .build();
  }

  MethodSpec modeledService(ServiceShape shape) {
    //   public static IKeyManagementServiceClient KeyManagementService(AWSKMS nativeValue) {
    //     return new Shim(nativeValue, null);
    //   }
    String methodName = capitalize(shape.toShapeId().getName());
    ClassName nativeClass = AwsSdkNativeV1.classNameForServiceClient(shape);
    ClassName dafnyClass = AwsSdkDafnyV1.classNameForAwsService(shape);
    ClassName shim = ShimV1.className(shape);
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
    return super.modeledEnum(shape);
  }

  /**
   * Should be called for all of a service's operations' outputs.
   */
  MethodSpec generateConvertResponseV1(final ShapeId shapeId) {
    MethodSpec structure = generateConvertStructure(shapeId);
    MethodSpec.Builder builder = structure.toBuilder();
    builder.parameters.clear();
    builder.addParameter(
      subject.nativeNameResolver.typeForOperationOutput(shapeId),
      "nativeValue"
    );
    return builder.build();
  }

  MethodSpec generateConvertStructure(final ShapeId shapeId) {
    final StructureShape structureShape = subject.model.expectShape(
      shapeId,
      StructureShape.class
    );
    return super.modeledStructure(structureShape);
  }

  MethodSpec generateConvertUnion(final ShapeId shapeId) {
    final UnionShape unionShape = subject.model.expectShape(
      shapeId,
      UnionShape.class
    );
    return super.modeledUnion(unionShape);
  }

  /** For AWS SDK structure members, the getter is `get + capitalized member name`. */
  @Override
  protected CodeBlock getMember(
    CodeBlock variableName,
    MemberShape memberShape
  ) {
    return CodeBlock.of(
      "$L.get$L()",
      variableName,
      capitalize(memberShape.getMemberName())
    );
  }

  /**
   * We have to customize
   * List conversion for the AWS SDK for Java V1 because
   * AWS SDK Java V1 treats Enums in a special way.
   * See the comment on
   * {@link AwsSdkNativeV1#typeForShapeNoEnum}
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
        memberConverter,
        getTypeDescriptor
      )
      .build();
  }

  /**
   * We have to customize
   * Set conversion for the AWS SDK for Java V1 because
   * AWS SDK Java V1 treats Enums in a special way.
   * See the comment on
   * {@link AwsSdkNativeV1#typeForShapeNoEnum}
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
   * Map conversion for the AWS SDK for Java V1 because
   * AWS SDK Java V1 treats Enums in a special way.
   * See the comment on
   * {@link AwsSdkNativeV1#typeForShapeNoEnum}
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

  MethodSpec generateConvertOpaqueError() {
    // Opaque Errors are not in the model,
    // so we cannot use any of our helper methods for this method.

    // This is memberDeclaration from above,
    // but with calls to target.dafnyNameResolver replaced with their expected response.
    CodeBlock memberDeclaration = CodeBlock.of(
      "$T $L",
      ParameterizedTypeName.get(
        ClassName.get("Wrappers_Compile", "Option"),
        ParameterizedTypeName.get(
          software.amazon.polymorph.smithyjava.nameresolver.Constants.DAFNY_SEQUENCE_CLASS_NAME,
          WildcardTypeName.subtypeOf(Character.class)
        )
      ),
      "message"
    );
    // This is memberAssignment from above,
    // but with calls to dafnyNameResolver replaced with their expected response.
    CodeBlock stringTypeDescriptor = Dafny.TYPE_DESCRIPTOR_BY_SHAPE_TYPE.get(
      ShapeType.STRING
    );
    CodeBlock memberAssignment = CodeBlock.of(
      "$L = $T.nonNull($L) ?\n$T.create_Some($L, $T.$L($L))\n: $T.create_None($L)",
      "message",
      ClassName.get(Objects.class),
      "nativeValue.getMessage()",
      ClassName.get("Wrappers_Compile", "Option"),
      stringTypeDescriptor,
      COMMON_TO_DAFNY_SIMPLE,
      SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE
        .get(ShapeType.STRING)
        .methodName(),
      "nativeValue.getMessage()",
      ClassName.get("Wrappers_Compile", "Option"),
      stringTypeDescriptor
    );
    return MethodSpec
      .methodBuilder("Error")
      .addModifiers(Modifier.PUBLIC, Modifier.STATIC)
      .returns(subject.dafnyNameResolver.abstractClassForError())
      .addParameter(
        subject.nativeNameResolver.baseErrorForService(),
        "nativeValue"
      )
      .addStatement(memberDeclaration)
      .addStatement(memberAssignment)
      .addStatement(
        "return new $T(message)",
        subject.dafnyNameResolver.classForOpaqueError()
      )
      .build();
  }
}
