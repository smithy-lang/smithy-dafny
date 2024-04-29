// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator;

import static software.amazon.smithy.utils.StringUtils.capitalize;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.MethodSpec;
import com.squareup.javapoet.ParameterSpec;
import com.squareup.javapoet.TypeName;
import java.util.Map;
import javax.annotation.Nonnull;
import javax.lang.model.element.Modifier;
import software.amazon.polymorph.smithyjava.BuilderSpecs;
import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.polymorph.smithyjava.NamespaceHelper;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject.AwsSdkVersion;
import software.amazon.polymorph.smithyjava.generator.awssdk.v1.ToNativeAwsV1;
import software.amazon.polymorph.smithyjava.generator.awssdk.v2.ToNativeAwsV2;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
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

public abstract class ToNative extends Generator {

  protected static final String VAR_INPUT = "dafnyValue";
  protected static final String TO_NATIVE = "ToNative";
  protected static final String NATIVE_BUILDER = "nativeBuilder";
  /**
   * The keys are the Dafny generated java input type,
   * the values are the method that converts from that input to the
   * idiomatic java type.
   */
  protected static final Map<
    ShapeType,
    MethodReference
  > AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE;
  protected static final Map<
    ShapeType,
    MethodReference
  > SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE;
  protected static final ClassName COMMON_TO_NATIVE_SIMPLE = ClassName.get(
    "software.amazon.smithy.dafny.conversion",
    "ToNative",
    "Simple"
  );
  protected static final ClassName COMMON_TO_NATIVE_AGGREGATE = ClassName.get(
    "software.amazon.smithy.dafny.conversion",
    "ToNative",
    "Aggregate"
  );

  static {
    AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE =
      Map.ofEntries(
        Map.entry(
          ShapeType.LIST,
          new MethodReference(COMMON_TO_NATIVE_AGGREGATE, "GenericToList")
        ),
        Map.entry(
          ShapeType.SET,
          new MethodReference(COMMON_TO_NATIVE_AGGREGATE, "GenericToSet")
        ),
        Map.entry(
          ShapeType.MAP,
          new MethodReference(COMMON_TO_NATIVE_AGGREGATE, "GenericToMap")
        )
      );
    SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE =
      Map.ofEntries(
        Map.entry(
          ShapeType.BLOB,
          new MethodReference(COMMON_TO_NATIVE_SIMPLE, "ByteBuffer")
        ),
        Map.entry(ShapeType.BOOLEAN, Constants.IDENTITY_FUNCTION),
        Map.entry(
          ShapeType.STRING,
          new MethodReference(COMMON_TO_NATIVE_SIMPLE, "String")
        ),
        // TODO: Timestamp should be service specific
        Map.entry(
          ShapeType.TIMESTAMP,
          new MethodReference(COMMON_TO_NATIVE_SIMPLE, "Date")
        ),
        Map.entry(ShapeType.BYTE, Constants.IDENTITY_FUNCTION),
        Map.entry(ShapeType.SHORT, Constants.IDENTITY_FUNCTION),
        Map.entry(ShapeType.INTEGER, Constants.IDENTITY_FUNCTION),
        Map.entry(ShapeType.LONG, Constants.IDENTITY_FUNCTION),
        Map.entry(
          ShapeType.DOUBLE,
          new MethodReference(COMMON_TO_NATIVE_SIMPLE, "Double")
        ),
        Map.entry(ShapeType.BIG_DECIMAL, Constants.IDENTITY_FUNCTION),
        Map.entry(ShapeType.BIG_INTEGER, Constants.IDENTITY_FUNCTION)
      );
  }

  /**
   * The class name of the Subject's Shim's ToNative class.
   */
  protected final ClassName thisClassName;

  public ToNative(CodegenSubject subject, ClassName className) {
    super(subject);
    thisClassName = className;
  }

  /** Signature of an Error conversion method. */
  protected MethodSpec.Builder initializeErrorMethodSpec(
    TypeName inputType,
    TypeName returnType
  ) {
    return initializeMethodSpec("Error", inputType, returnType);
  }

  /** Signature of a ToNative conversion method. */
  protected MethodSpec.Builder initializeMethodSpec(
    String methodName,
    TypeName inputType,
    TypeName returnType
  ) {
    return MethodSpec
      .methodBuilder(methodName)
      .returns(returnType)
      .addModifiers(PUBLIC_STATIC)
      .addParameter(inputType, VAR_INPUT);
  }

  /** Declare and assign the native value's builder. */
  protected MethodSpec.Builder createNativeBuilder(
    MethodSpec.Builder method,
    ClassName returnType
  ) {
    return method.addStatement(
      "$T $L = $T.$L()",
      BuilderSpecs.builderInterfaceName(returnType),
      NATIVE_BUILDER,
      returnType,
      BuilderSpecs.BUILDER_VAR
    );
  }

  /** Return invocation of nativeBuilder's build method. */
  protected MethodSpec buildAndReturn(MethodSpec.Builder method) {
    method.addStatement("return $L.build()", NATIVE_BUILDER);
    return method.build();
  }

  @SuppressWarnings("OptionalGetWithoutIsPresent")
  protected MethodSpec modeledMap(MapShape shape) {
    Shape keyShape = subject.model.expectShape(
      shape.getKey().asMemberShape().get().getTarget()
    );
    CodeBlock keyConverter = conversionMethodReference(keyShape)
      .asFunctionalReference();
    Shape valueShape = subject.model.expectShape(
      shape.getValue().asMemberShape().get().getTarget()
    );
    CodeBlock valueConverter = conversionMethodReference(valueShape)
      .asFunctionalReference();
    CodeBlock genericCall = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE
      .get(shape.getType())
      .asNormalReference();
    ParameterSpec parameterSpec = ParameterSpec
      .builder(subject.dafnyNameResolver.typeForShape(shape.getId()), VAR_INPUT)
      .build();
    return MethodSpec
      .methodBuilder(capitalize(shape.getId().getName()))
      .addModifiers(Modifier.PUBLIC, Modifier.STATIC)
      .returns(subject.nativeNameResolver.typeForShape(shape.getId()))
      .addParameter(parameterSpec)
      .addStatement(
        "return $L(\n$L, \n$L, \n$L)",
        genericCall,
        VAR_INPUT,
        keyConverter,
        valueConverter
      )
      .build();
  }

  /** Uses a Builder to build the native value of Structure. */
  protected MethodSpec modeledStructure(StructureShape structureShape) {
    final ShapeId shapeId = structureShape.getId();
    final String methodName = capitalize(shapeId.getName());
    final TypeName inputType = subject.dafnyNameResolver.typeForShape(shapeId);
    final ClassName returnType =
      subject.nativeNameResolver.classNameForStructure(structureShape);
    MethodSpec.Builder method = initializeMethodSpec(
      methodName,
      inputType,
      returnType
    );
    createNativeBuilder(method, returnType);
    // For each member
    structureShape
      .members()
      .forEach(member -> {
        // if optional, check if present
        if (member.isOptional()) {
          method.beginControlFlow(
            "if ($L.$L.is_Some())",
            VAR_INPUT,
            Dafny.getMemberField(member)
          );
        }
        method.addStatement(
          setWithConversionCall(member, Dafny.getMemberFieldValue(member))
        );
        if (member.isOptional()) {
          method.endControlFlow();
        }
      });
    return buildAndReturn(method);
  }

  protected MethodSpec modeledError(final ShapeId shapeId) {
    return modeledError(
      subject.model.expectShape(shapeId, StructureShape.class)
    );
  }

  /** Uses a Builder to build the native value of Error. */
  protected MethodSpec modeledError(final StructureShape shape) {
    MethodSpec structure = modeledStructure(shape);
    MethodSpec.Builder builder = structure.toBuilder();
    builder.setName("Error");
    builder.returns(subject.nativeNameResolver.classNameForStructure(shape));
    return builder.build();
  }

  protected MethodSpec modeledEnum(Shape shape) {
    final ClassName returnType = subject.nativeNameResolver.classForEnum(shape);
    MethodSpec.Builder method = modeledEnumCommon(shape, returnType);
    // No Enum value matched, throw an Exception
    method.addStatement(
      "throw new $T($S + $L)",
      IllegalArgumentException.class,
      "No entry of %s matches the input : ".formatted(returnType),
      VAR_INPUT
    );
    return method.build();
  }

  /** @return MethodSpec.Builder with an If-Return for every known enum value.*/
  protected final MethodSpec.Builder modeledEnumCommon(
    Shape shape,
    ClassName returnType
  ) {
    final ShapeId shapeId = shape.getId();
    final String methodName = capitalize(shapeId.getName());
    final TypeName inputType = subject.dafnyNameResolver.typeForShape(shapeId);
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
          .addStatement("return $T.$L", returnType, name)
          .endControlFlow()
      );
    return method;
  }

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
    createNativeBuilder(method, returnType);
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
    return buildAndReturn(method);
  }

  protected MethodSpec modeledList(ListShape shape) {
    return modeledListOrSet(shape.getMember(), shape.getId(), shape.getType());
  }

  protected MethodSpec modeledSet(SetShape shape) {
    return modeledListOrSet(shape.getMember(), shape.getId(), shape.getType());
  }

  protected MethodSpec modeledListOrSet(
    MemberShape memberShape,
    ShapeId shapeId,
    ShapeType shapeType
  ) {
    CodeBlock memberConverter = conversionMethodReference(
      subject.model.expectShape(memberShape.getTarget())
    )
      .asFunctionalReference();
    CodeBlock genericCall = AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE
      .get(shapeType)
      .asNormalReference();
    ParameterSpec parameterSpec = ParameterSpec
      .builder(subject.dafnyNameResolver.typeForShape(shapeId), VAR_INPUT)
      .build();
    return MethodSpec
      .methodBuilder(capitalize(shapeId.getName()))
      .addModifiers(PUBLIC_STATIC)
      .returns(subject.nativeNameResolver.typeForShape(shapeId))
      .addParameter(parameterSpec)
      .addStatement(
        "return $L(\n$L, \n$L)",
        genericCall,
        VAR_INPUT,
        memberConverter
      )
      .build();
  }

  /** @param getMember can be a Variable or a method call that returns the member value.*/
  protected CodeBlock setWithConversionCall(
    MemberShape member,
    CodeBlock getMember
  ) {
    return CodeBlock.of(
      "$L.$L($L($L.$L))",
      NATIVE_BUILDER,
      setMemberField(member),
      conversionMethodReference(subject.model.expectShape(member.getTarget()))
        .asNormalReference(),
      VAR_INPUT,
      getMember
    );
  }

  /**
   * This logic assumes we are setting a parameter on a builder
   * generated by BuilderSpecs or something equivalent.
   * @return CodeBlock of Method to set a member field. */
  protected CodeBlock setMemberField(MemberShape shape) {
    return CodeBlock.of("$L", shape.getMemberName());
  }

  /**
   * Returns MethodReference that converts from
   * the Java Dafny shape to
   * the Java Native shape.
   */
  @SuppressWarnings({ "DuplicatedCode" })
  protected MethodReference conversionMethodReference(Shape shape) {
    if (shape.isMemberShape()) {
      throw new IllegalArgumentException(
        "MemberShapes MUST BE de-referenced BEFORE calling ToNative.conversionMethodReference."
      );
    }
    // If the target is simple, use SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE
    if (ModelUtils.isSmithyApiOrSimpleShape(shape)) {
      return SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(shape.getType());
    }
    return nonSimpleConversionMethodReference(shape);
  }

  @Nonnull
  protected MethodReference nonSimpleConversionMethodReference(
    Shape targetShape
  ) {
    ShapeId targetId = targetShape.getId();
    final String methodName = capitalize(targetId.getName());
    final ClassName toNativeClassName = ToNativeClassNameForShape(
      targetShape,
      subject.sdkVersion
    );
    return new MethodReference(toNativeClassName, methodName);
  }

  public static ClassName ToNativeClassNameForShape(
    final Shape targetShape,
    final AwsSdkVersion sdkVersion
  ) {
    ShapeId targetId = targetShape.getId();
    // if in AWS SDK namespace, reference ToNative from AWS SDK
    if (AwsSdkNameResolverHelpers.isInAwsSdkNamespace(targetId)) {
      return switch (sdkVersion) {
        case V1 -> ToNativeAwsV1.className(targetId);
        case V2 -> ToNativeAwsV2.className(targetId);
      };
    }
    // Otherwise, must be one of our Local Service's
    return ClassName.get(
      NamespaceHelper.standardize(targetId.getNamespace()),
      TO_NATIVE
    );
  }
}
