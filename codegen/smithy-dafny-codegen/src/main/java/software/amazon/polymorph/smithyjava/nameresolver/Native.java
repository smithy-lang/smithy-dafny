// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava.nameresolver;

import static software.amazon.smithy.utils.StringUtils.capitalize;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.ParameterizedTypeName;
import com.squareup.javapoet.TypeName;
import java.math.BigDecimal;
import java.math.BigInteger;
import java.nio.ByteBuffer;
import java.time.Instant;
import java.util.Date;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import javax.annotation.Nullable;
import software.amazon.polymorph.smithydafny.DafnyNameResolver;
import software.amazon.polymorph.smithyjava.NamespaceHelper;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.polymorph.smithyjava.unmodeled.OpaqueError;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ShapeType;
import software.amazon.smithy.model.traits.BoxTrait;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.StreamingTrait;

/**
 * Provides a consistent mapping between names of
 * model Shapes and generated identifiers in Java
 * for the native Java code.
 */
public class Native extends NameResolver {

  protected static final Map<
    String,
    TypeName
  > NATIVE_TYPES_BY_SMITHY_PRELUDE_SHAPE_NAME;
  protected static final Map<
    ShapeType,
    TypeName
  > NATIVE_TYPES_BY_SIMPLE_SHAPE_TYPE;

  static {
    NATIVE_TYPES_BY_SMITHY_PRELUDE_SHAPE_NAME =
      Map.ofEntries(
        Map.entry("String", ClassName.get(String.class)),
        Map.entry("Blob", ClassName.get(ByteBuffer.class)),
        Map.entry("Boolean", TypeName.BOOLEAN.box()),
        Map.entry("PrimitiveBoolean", TypeName.BOOLEAN),
        Map.entry("Byte", TypeName.BYTE.box()),
        Map.entry("PrimitiveByte", TypeName.BYTE),
        Map.entry("Short", TypeName.SHORT.box()),
        Map.entry("PrimitiveShort", TypeName.SHORT),
        Map.entry("Integer", TypeName.INT.box()),
        Map.entry("PrimitiveInteger", TypeName.INT),
        Map.entry("Long", TypeName.LONG.box()),
        Map.entry("PrimitiveLong", TypeName.LONG),
        Map.entry("Float", TypeName.FLOAT.box()),
        Map.entry("PrimitiveFloat", TypeName.FLOAT),
        Map.entry("Double", TypeName.DOUBLE.box()),
        Map.entry("PrimitiveDouble", TypeName.DOUBLE),
        Map.entry("Timestamp", ClassName.get(Instant.class))
      );
    NATIVE_TYPES_BY_SIMPLE_SHAPE_TYPE =
      Map.ofEntries(
        Map.entry(ShapeType.BLOB, ClassName.get(ByteBuffer.class)),
        Map.entry(ShapeType.BOOLEAN, TypeName.BOOLEAN),
        Map.entry(ShapeType.BYTE, TypeName.BYTE),
        Map.entry(ShapeType.SHORT, TypeName.SHORT),
        Map.entry(ShapeType.INTEGER, TypeName.INT),
        Map.entry(ShapeType.LONG, TypeName.LONG),
        Map.entry(ShapeType.FLOAT, TypeName.FLOAT),
        Map.entry(ShapeType.DOUBLE, TypeName.DOUBLE),
        // TODO: AWS SDK V2 uses Instant, not Date
        Map.entry(ShapeType.TIMESTAMP, ClassName.get(Date.class)),
        Map.entry(ShapeType.BIG_DECIMAL, ClassName.get(BigDecimal.class)),
        Map.entry(ShapeType.BIG_INTEGER, ClassName.get(BigInteger.class))
      );
  }

  public Native(
    final String packageName,
    final ServiceShape serviceShape,
    final Model model,
    final String modelPackageName,
    CodegenSubject.AwsSdkVersion awsSdkVersion
  ) {
    super(packageName, serviceShape, model, modelPackageName, awsSdkVersion);
  }

  public static String aggregateSizeMethod(ShapeType shapeType) {
    return switch (shapeType) {
      case LIST, SET, MAP -> "size()";
      case STRING -> "length()";
      // This is complicated: A (Byte)Buffer has four landmark indexes:
      // mark <= position <= limit <= capacity
      // Let us ASSUME that we are validating a buffer that has been
      // written to but not read from, and thus the `remaining` bytes
      // (limit - position) is the length.
      case BLOB -> "remaining()";
      case MEMBER -> throw new IllegalArgumentException(
        """
        ShapeType is not defined on MemberShapes but on their target.
        The target MUST be looked up with the model.
        See software.amazon.polymorph.smithyjava.PolymorphFieldSpec.getTargetShape.
        """
      );
      default -> throw new IllegalStateException(
        "aggregateSizeMethod only accepts LIST, SET, MAP, STRING, or BLOB. Got : " +
        shapeType
      );
    };
  }

  /**
   * Returns the Native type corresponding to the given shape.
   */
  @SuppressWarnings("OptionalGetWithoutIsPresent")
  public TypeName typeForShape(final ShapeId shapeId) {
    final Shape shape = model.expectShape(shapeId);

    // First check if this is a built-in Smithy shape. If so, we just map it to the native type and return
    if (ModelUtils.isSmithyApiShape(shapeId)) {
      @Nullable
      final TypeName typeName = NATIVE_TYPES_BY_SMITHY_PRELUDE_SHAPE_NAME.get(
        shapeId.getName()
      );
      return Objects.requireNonNull(
        typeName,
        () -> String.format("No native type for prelude shape %s", shapeId)
      );
    }

    return switch (shape.getType()) {
      case BOOLEAN, BYTE, SHORT, INTEGER, LONG, FLOAT, DOUBLE -> {
        /* From the Smithy Docs:
         * "Boolean, byte, short, integer, long, float, and double shapes
         * are only considered boxed if they are marked with the box trait.
         * All other shapes are always considered boxed."
         * https://smithy.io/1.0/spec/core/type-refinement-traits.html#box-trait
         * While Smithy Models SHOULD use Smithy Prelude shapes to avoid this confusion,
         * they do not have to.
         * Hence, the need to check if these shapes have the box trait
         */
        final TypeName typeName = NATIVE_TYPES_BY_SIMPLE_SHAPE_TYPE.get(
          shape.getType()
        );
        yield shape.hasTrait(BoxTrait.class) ? typeName.box() : typeName;
      }
      // For supported simple shapes, just map to native types
      case BLOB,
        TIMESTAMP,
        BIG_DECIMAL,
        BIG_INTEGER -> NATIVE_TYPES_BY_SIMPLE_SHAPE_TYPE.get(shape.getType());
      case STRING, ENUM -> classForStringOrEnum(shape);
      case LIST -> ParameterizedTypeName.get(
        ClassName.get(List.class),
        typeForShape(shape.asListShape().get().getMember().getTarget())
      );
      case MAP -> ParameterizedTypeName.get(
        ClassName.get(Map.class),
        typeForShape(shape.asMapShape().get().getKey().getTarget()),
        typeForShape(shape.asMapShape().get().getValue().getTarget())
      );
      case SET -> ParameterizedTypeName.get(
        ClassName.get(Set.class),
        typeForShape(shape.asSetShape().get().getMember().getTarget())
      );
      case MEMBER -> typeForShape(shape.asMemberShape().get().getTarget());
      case STRUCTURE -> classNameForStructure(shape.asStructureShape().get());
      case SERVICE -> classNameForService(shape.asServiceShape().get());
      case RESOURCE -> classNameForResource(shape.asResourceShape().get());
      // Unions are identical to Structures (in this context)
      case UNION -> classNameForStructure(shape.asUnionShape().get());
      default -> throw new UnsupportedOperationException(
        "Shape %s has unsupported type %s".formatted(shapeId, shape.getType())
      );
    };
  }

  public ClassName classForStringOrEnum(final Shape shape) {
    // This case must be first because shape can be an @enum string, or a Smithy 2.0 enum
    if (shape.hasTrait(EnumTrait.class)) {
      if (AwsSdkNameResolverHelpers.isInAwsSdkNamespace(shape.getId())) {
        return classNameForAwsSdkShape(shape);
      }
      return classForEnum(shape);
    }

    if (shape.getType().isShapeType(ShapeType.STRING)) {
      return classForString();
    }

    throw new IllegalArgumentException("Shape was neither string nor enum");
  }

  public ClassName classForEnum(final Shape shape) {
    if (isInServiceNameSpace(shape.getId())) {
      return ClassName.get(modelPackage, shape.getId().getName());
    }
    // For every AWS SDK Java Library and every Library Polymorph generates,
    // POJOs (smithy structures),
    // most Exceptions (also structures),
    // and interfaces (smithy resources or services)
    // are placed in a model sub-package.
    return ClassName.get(
      NamespaceHelper.standardize(shape.getId().getNamespace()) + ".model",
      shape.getId().getName()
    );
  }

  public ClassName classForString() {
    return ClassName.get(String.class);
  }

  public ClassName classForDouble() {
    return ClassName.get(Double.class);
  }

  @SuppressWarnings("OptionalGetWithoutIsPresent")
  public TypeName typeForListOrSetMember(ShapeId shapeId) {
    Shape shape = model.expectShape(shapeId);
    return switch (shape.getType()) {
      case MEMBER -> typeForShape(shape.getId());
      case LIST -> typeForShape(
        shape.asListShape().get().getMember().getTarget()
      );
      case SET -> typeForShape(
        shape.asSetShape().get().getMember().getTarget()
      );
      default -> throw new IllegalStateException(
        "typeForListOrSetMember only accepts MEMBER, LIST, or SET. Got: " +
        shape.getType()
      );
    };
  }

  public ClassName classNameForStructure(Shape shape) {
    if (!(shape.isUnionShape() || shape.isStructureShape())) {
      throw new IllegalArgumentException(
        "typeForStructure should only be called for Structures or Unions. ShapeId: %s".formatted(
            shape.getId()
          )
      );
    }
    if (shape.hasTrait(ReferenceTrait.class)) {
      final ReferenceTrait reference = shape.expectTrait(ReferenceTrait.class);
      // A service or resource in a structure should almost always be treated as the interface
      Shape rShape = model.expectShape(reference.getReferentId());
      return classNameForInterfaceOrLocalService(rShape, this.awsSdkVersion);
    }
    if (AwsSdkNameResolverHelpers.isInAwsSdkNamespace(shape.getId())) {
      return classNameForAwsSdkShape(shape);
    }
    if (isInServiceNameSpace(shape.getId())) {
      return ClassName.get(modelPackage, shape.getId().getName());
    }
    // For every AWS SDK Java Library and every Library Polymorph generates,
    // POJOs (smithy structures),
    // most Exceptions (also structures),
    // are placed in a model sub-package.
    return ClassName.get(
      NamespaceHelper.standardize(shape.getId().getNamespace()) + ".model",
      shape.getId().getName()
    );
  }

  public ClassName classNameForService(ServiceShape shape) {
    return classNameForInterfaceOrLocalService(shape, this.awsSdkVersion);
  }

  public ClassName classNameForTestService(ServiceShape shape) {
    Optional<LocalServiceTrait> maybeTrait = shape.getTrait(
      LocalServiceTrait.class
    );
    if (maybeTrait.isEmpty()) {
      throw new IllegalArgumentException(
        ("ServiceShape for local-service-test MUST have LocalTrait." +
          " ShapeId: %s").formatted(shape.toShapeId())
      );
    }
    final String namespace =
      NamespaceHelper.standardize(shape.getId().getNamespace()) + ".wrapped";
    return ClassName.get(
      namespace,
      "Test" + capitalize(maybeTrait.get().getSdkId())
    );
  }

  public static ClassName classNameForResourceInterface(ResourceShape shape) {
    return ClassName.get(
      NamespaceHelper.standardize(shape.getId().getNamespace()),
      DafnyNameResolver.traitNameForResource(shape)
    );
  }

  public static ClassName classNameForInterfaceOrLocalService(
    Shape shape,
    CodegenSubject.AwsSdkVersion sdkVersion
  ) {
    if (AwsSdkNameResolverHelpers.isInAwsSdkNamespace(shape.toShapeId())) {
      return classNameForAwsSdk(shape, sdkVersion);
    }
    // if operation takes a non-AWS Service/Resource, return Native Interface Or Local Service
    if (shape.isResourceShape()) {
      //noinspection OptionalGetWithoutIsPresent
      return classNameForResourceInterface(shape.asResourceShape().get());
    }
    if (shape.isServiceShape()) {
      Optional<LocalServiceTrait> maybeTrait = shape.getTrait(
        LocalServiceTrait.class
      );
      if (maybeTrait.isEmpty()) {
        throw new IllegalArgumentException(
          ("non AWS-Service ServiceShapes MUST have LocalTrait." +
            " ShapeId: %s").formatted(shape.toShapeId())
        );
      }
      return ClassName.get(
        NamespaceHelper.standardize(shape.getId().getNamespace()),
        maybeTrait.get().getSdkId()
      );
    }
    throw new IllegalArgumentException(
      "Polymorph only supports interfaces for Service & Resource Shapes. ShapeId: %s".formatted(
          shape.toShapeId()
        )
    );
  }

  public static ClassName classNameForAwsSdk(
    Shape shape,
    CodegenSubject.AwsSdkVersion sdkVersion
  ) {
    if (shape.getType() != ShapeType.SERVICE) {
      throw new RuntimeException(
        "Polymorph only knows the class Name of Service clients. " +
        "Would a TypeName suffice? ShapeId: " +
        shape.toShapeId()
      );
    }
    @SuppressWarnings("OptionalGetWithoutIsPresent")
    ServiceShape service = shape.asServiceShape().get();
    return switch (sdkVersion) {
      case V1 -> AwsSdkNativeV1.classNameForServiceClient(service);
      case V2 -> AwsSdkNativeV2.classNameForServiceClient(service);
    };
  }

  public ClassName classNameForResource(ResourceShape shape) {
    return ClassName.get(
      NamespaceHelper.standardize(shape.getId().getNamespace()),
      shape.getId().getName()
    );
  }

  // TODO: improve exceptions for local services
  public ClassName baseErrorForService() {
    throw new IllegalArgumentException(
      "Local Services no longer have a local error hierarchy." +
      "Use `ClassName.get(RuntimeException.class)` instead."
    );
  }

  protected ClassName classNameForAwsSdkShape(final Shape shape) {
    // This is inefficient, but we currently instantiate Native for local services
    // but then call this method that should only be relevant for AWS SDK wrappers.
    // It would be better to make Native abstract in the future.
    return switch (awsSdkVersion) {
      case V1 -> new AwsSdkNativeV1(serviceShape, model)
        .classNameForAwsSdkShape(shape);
      case V2 -> new AwsSdkNativeV2(serviceShape, model)
        .classNameForAwsSdkShape(shape);
    };
  }
}
