// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.generator;

import static software.amazon.smithy.utils.StringUtils.capitalize;
import static software.amazon.smithy.utils.StringUtils.uncapitalize;

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
import javax.annotation.Nonnull;
import javax.lang.model.element.Modifier;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import software.amazon.polymorph.smithyjava.MethodReference;
import software.amazon.polymorph.smithyjava.NamespaceHelper;
import software.amazon.polymorph.smithyjava.generator.awssdk.v1.ToDafnyAwsV1;
import software.amazon.polymorph.smithyjava.generator.awssdk.v2.ToDafnyAwsV2;
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

public abstract class ToDafny extends Generator {

  @SuppressWarnings("unused")
  private static final Logger LOGGER = LoggerFactory.getLogger(ToDafny.class);

  /**
   * The keys are the input type, the values are the method that converts from that input to the Dafny type
   */
  protected static final Map<
    ShapeType,
    MethodReference
  > AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE;
  protected static final Map<
    ShapeType,
    MethodReference
  > SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE;
  protected static final ClassName COMMON_TO_DAFNY_SIMPLE = ClassName.get(
    "software.amazon.smithy.dafny.conversion",
    "ToDafny",
    "Simple"
  );
  protected static final ClassName COMMON_TO_DAFNY_AGGREGATE = ClassName.get(
    "software.amazon.smithy.dafny.conversion",
    "ToDafny",
    "Aggregate"
  );
  protected static final String VAR_INPUT = "nativeValue";
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
    AGGREGATE_CONVERSION_METHOD_FROM_SHAPE_TYPE =
      Map.ofEntries(
        Map.entry(
          ShapeType.LIST,
          new MethodReference(COMMON_TO_DAFNY_AGGREGATE, "GenericToSequence")
        ),
        Map.entry(
          ShapeType.SET,
          new MethodReference(COMMON_TO_DAFNY_AGGREGATE, "GenericToSet")
        ),
        Map.entry(
          ShapeType.MAP,
          new MethodReference(COMMON_TO_DAFNY_AGGREGATE, "GenericToMap")
        )
      );
    SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE =
      Map.ofEntries(
        Map.entry(
          ShapeType.BLOB,
          new MethodReference(COMMON_TO_DAFNY_SIMPLE, "ByteSequence")
        ),
        Map.entry(ShapeType.BOOLEAN, Constants.IDENTITY_FUNCTION),
        Map.entry(
          ShapeType.STRING,
          new MethodReference(COMMON_TO_DAFNY_SIMPLE, "CharacterSequence")
        ),
        Map.entry(
          ShapeType.TIMESTAMP,
          new MethodReference(COMMON_TO_DAFNY_SIMPLE, "CharacterSequence")
        ),
        Map.entry(ShapeType.BYTE, Constants.IDENTITY_FUNCTION),
        Map.entry(ShapeType.SHORT, Constants.IDENTITY_FUNCTION),
        Map.entry(ShapeType.INTEGER, Constants.IDENTITY_FUNCTION),
        Map.entry(ShapeType.LONG, Constants.IDENTITY_FUNCTION),
        Map.entry(
          ShapeType.DOUBLE,
          new MethodReference(COMMON_TO_DAFNY_SIMPLE, "Double")
        ),
        Map.entry(ShapeType.BIG_DECIMAL, Constants.IDENTITY_FUNCTION),
        Map.entry(ShapeType.BIG_INTEGER, Constants.IDENTITY_FUNCTION)
      );
  }

  protected MethodSpec modeledStructure(final StructureShape structureShape) {
    final ShapeId shapeId = structureShape.getId();
    String methodName = capitalize(structureShape.getId().getName());
    MethodSpec.Builder builder = MethodSpec
      .methodBuilder(methodName)
      .addModifiers(PUBLIC_STATIC)
      .returns(subject.dafnyNameResolver.typeForShape(shapeId))
      .addParameter(
        subject.nativeNameResolver.classNameForStructure(structureShape),
        VAR_INPUT
      );

    if (structureShape.members().size() == 0) {
      builder.addStatement(
        "return new $T()",
        subject.dafnyNameResolver.typeForShape(shapeId)
      );
      return builder.build();
    }
    List<CodeBlock> variables = new ArrayList<>(
      structureShape.members().size()
    );
    structureShape
      .members()
      .forEach(memberShape -> {
        CodeBlock varOut = CodeBlock.of(
          "$L",
          uncapitalize(memberShape.getMemberName())
        );
        CodeBlock varIn = getMember(CodeBlock.of(VAR_INPUT), memberShape);
        builder.addStatement(memberDeclaration(memberShape, varOut));
        builder.addStatement(
          memberConvertAndAssign(memberShape, varOut, varIn)
        );
        variables.add(varOut);
      });
    builder.addStatement(
      "return new $T($L)",
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
      .addParameter(
        subject.nativeNameResolver.classNameForStructure(shape),
        VAR_INPUT
      );
    boolean isRecordType = shape.members().size() == 1;
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
          isRecordType
        );
        method
          .beginControlFlow("if ($T.nonNull($L))", Objects.class, getField)
          .addStatement(
            "return $T.$L($L)",
            returnType,
            datatypeConstructorCreate,
            memberConversion
          )
          .endControlFlow();
      });
    method.addStatement(
      "throw new $T($S + $L + $S)",
      IllegalArgumentException.class,
      "Cannot convert ",
      VAR_INPUT,
      " to %s.".formatted(returnType)
    );
    return method.build();
  }

  protected CodeBlock memberDeclaration(
    final MemberShape memberShape,
    CodeBlock variable
  ) {
    if (memberShape.isRequired()) {
      return CodeBlock.of(
        "$T $L",
        subject.dafnyNameResolver.typeForShape(memberShape.getId()),
        variable
      );
    }
    return CodeBlock.of(
      "$T $L",
      ParameterizedTypeName.get(
        ClassName.get("Wrappers_Compile", "Option"),
        subject.dafnyNameResolver.typeForShape(memberShape.getId())
      ),
      variable
    );
  }

  /** @return CodeBlock invoking member Conversion and assigning the output. */
  protected CodeBlock memberConvertAndAssign(
    final MemberShape memberShape,
    CodeBlock outputVar,
    CodeBlock inputVar
  ) {
    return memberAssign(
      memberShape,
      outputVar,
      inputVar,
      memberConversion(memberShape, inputVar)
    );
  }

  /** @return CodeBlock assigning result of member conversion to variable. */
  protected CodeBlock memberAssign(
    final MemberShape memberShape,
    CodeBlock outputVar,
    CodeBlock inputVar,
    CodeBlock memberConversion
  ) {
    if (memberShape.isRequired()) {
      return CodeBlock.of("$L = $L", outputVar, memberConversion);
    }
    final CodeBlock isNullCheck = CodeBlock.of(
      "$T.nonNull($L)",
      ClassName.get(Objects.class),
      inputVar
    );
    CodeBlock isSetCheck = isNullCheck;
    Shape targetShape = subject.model.expectShape(memberShape.getTarget());
    if (Constants.LIST_MAP_SET_SHAPE_TYPES.contains(targetShape.getType())) {
      isSetCheck = CodeBlock.of("($L && $L.size() > 0)", isNullCheck, inputVar);
    }
    CodeBlock typeDescriptor = subject.dafnyNameResolver.typeDescriptor(
      memberShape.getTarget()
    );
    return CodeBlock.of(
      "$L = $L ?\n$L\n: $L",
      outputVar,
      isSetCheck,
      subject.dafnyNameResolver.createSome(typeDescriptor, memberConversion),
      subject.dafnyNameResolver.createNone(typeDescriptor)
    );
  }

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
          .beginControlFlow("case $L:", name)
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
        subject.nativeNameResolver.typeForShape(shape.getId()),
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
        subject.nativeNameResolver.typeForShape(shape.getId()),
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
        subject.nativeNameResolver.typeForShape(shape.getId()),
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

  /** AWS SDK V1 uses a different getter pattern than Library (or, possibly, SDK V2) */
  protected abstract CodeBlock getMember(
    CodeBlock variableName,
    MemberShape memberShape
  );

  /** CodeBlock invoking the member conversion method. */
  protected CodeBlock memberConversion(
    MemberShape memberShape,
    CodeBlock inputVar
  ) {
    return CodeBlock.of(
      "$L($L)",
      conversionMethodReference(
        subject.model.expectShape(memberShape.getTarget())
      )
        .asNormalReference(),
      inputVar
    );
  }

  /**
   * Returns MethodReference that converts from
   * the Java Native Shape to
   * the Java Dafny Shape.
   */
  @SuppressWarnings({ "DuplicatedCode" })
  protected MethodReference conversionMethodReference(Shape shape) {
    if (shape.isMemberShape()) {
      throw new IllegalArgumentException(
        "MemberShapes MUST BE de-referenced BEFORE calling ToDafny.conversionMethodReference. ShapeId: %s".formatted(
            shape.toShapeId()
          )
      );
    }
    // If the target is simple, use SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE
    if (ModelUtils.isSmithyApiOrSimpleShape(shape)) {
      return SIMPLE_CONVERSION_METHOD_FROM_SHAPE_TYPE.get(shape.getType());
    }
    return nonSimpleConversionMethodReference(shape);
  }

  @SuppressWarnings("DuplicatedCode")
  @Nonnull
  protected MethodReference nonSimpleConversionMethodReference(Shape shape) {
    ShapeId targetId = shape.getId();
    final String methodName = capitalize(targetId.getName());
    // if in AWS SDK namespace, reference converter from AWS SDK ToDafny class
    if (AwsSdkNameResolverHelpers.isInAwsSdkNamespace(targetId)) {
      return switch (subject.sdkVersion) {
        case V1 -> new MethodReference(
          ToDafnyAwsV1.className(targetId),
          methodName
        );
        case V2 -> new MethodReference(
          ToDafnyAwsV2.className(targetId),
          methodName
        );
      };
    }
    // Otherwise, this target must be in another namespace,
    // reference converter from that namespace's ToDafny class
    ClassName otherNamespaceToDafny = ClassName.get(
      NamespaceHelper.standardize(targetId.getNamespace()),
      TO_DAFNY
    );
    return new MethodReference(otherNamespaceToDafny, methodName);
  }

  protected MethodSpec modeledError(final ShapeId shapeId) {
    return modeledError(
      subject.model.expectShape(shapeId, StructureShape.class)
    );
  }

  protected MethodSpec modeledError(final StructureShape shape) {
    MethodSpec structure = modeledStructure(shape);
    MethodSpec.Builder builder = structure.toBuilder();
    builder.setName("Error");
    builder.returns(subject.dafnyNameResolver.abstractClassForError());
    return builder.build();
  }
}
