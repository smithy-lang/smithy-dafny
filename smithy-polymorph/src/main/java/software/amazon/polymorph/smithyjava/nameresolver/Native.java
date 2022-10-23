package software.amazon.polymorph.smithyjava.nameresolver;

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
import java.util.Set;

import javax.annotation.Nullable;

import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ShapeType;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.BoxTrait;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.utils.StringUtils;

import static software.amazon.polymorph.smithyjava.nameresolver.Constants.SHAPE_TYPES_LIST_SET;
import static software.amazon.smithy.utils.StringUtils.capitalize;


/**
 * Provides a consistent mapping between names of
 * model Shapes and generated identifiers in Java
 * for the native Java code.
 */
public class Native extends NameResolver{
    protected static final Map<String, TypeName> NATIVE_TYPES_BY_SMITHY_PRELUDE_SHAPE_NAME;
    protected static final Map<ShapeType, TypeName> NATIVE_TYPES_BY_SIMPLE_SHAPE_TYPE;

    static {
        NATIVE_TYPES_BY_SMITHY_PRELUDE_SHAPE_NAME = Map.ofEntries(
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
        NATIVE_TYPES_BY_SIMPLE_SHAPE_TYPE = Map.ofEntries(
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
            final String modelPackageName
    ) {
        super(
                packageName,
                serviceShape,
                model,
                modelPackageName
        );
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
            default -> throw new IllegalStateException(
                    "aggregateSizeMethod only accepts LIST, SET, MAP, STRING, or BLOB. Got : " + shapeType);
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
            @Nullable final TypeName typeName = NATIVE_TYPES_BY_SMITHY_PRELUDE_SHAPE_NAME.get(shapeId.getName());
            return Objects.requireNonNull(typeName,
                    () -> String.format("No native type for prelude shape %s", shapeId));
        }

        return switch (shape.getType()) {
            case BOOLEAN, BYTE, SHORT, INTEGER, LONG, FLOAT, DOUBLE -> {
                /* From the Smithy Docs:
                 * "Boolean, byte, short, integer, long, float, and double shapes
                 * are only considered boxed if they are marked with the box trait.
                 * All other shapes are always considered boxed."
                 * https://awslabs.github.io/smithy/1.0/spec/core/type-refinement-traits.html#box-trait
                 * While Smithy Models SHOULD use Smithy Prelude shapes to avoid this confusion,
                 * they do not have to.
                 * Hence, the need to check if these shapes have the box trait
                 */
                final TypeName typeName = NATIVE_TYPES_BY_SIMPLE_SHAPE_TYPE.get(shape.getType());
                yield shape.hasTrait(BoxTrait.class) ? typeName.box() : typeName;
            }
            // For supported simple shapes, just map to native types
            case BLOB, TIMESTAMP, BIG_DECIMAL, BIG_INTEGER -> NATIVE_TYPES_BY_SIMPLE_SHAPE_TYPE.get(shape.getType());
            case STRING -> classForStringOrEnum(shape.asStringShape().get());
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
            case STRUCTURE -> typeForStructure(shape.asStructureShape().get());
            case SERVICE -> typeForService(shape.asServiceShape().get());
            case RESOURCE -> typeForResource(shape.asResourceShape().get());
            /* TODO: Handle Unions
            case UNION -> baseTypeForUnion(shape.asUnionShape().get());
            */
            default -> throw new UnsupportedOperationException("Shape %s has unsupported type %s"
                    .formatted(shapeId, shape.getType()));
        };
    }

    public ClassName classForStringOrEnum(final StringShape shape) {
        if (shape.hasTrait(EnumTrait.class)) {
            return classForEnum(shape);
        }
        return classForString();
    }

    public ClassName classForEnum(final Shape shape) {
        return ClassName.get(modelPackage, capitalize(shape.getId().getName()));
    }

    public ClassName classForString() {
        return ClassName.get(String.class);
    }

    @SuppressWarnings("OptionalGetWithoutIsPresent")
    ParameterizedTypeName typeForListOrSetNoEnum(final ShapeId shapeId) {
        final Shape shape = model.getShape(shapeId)
                .orElseThrow(() -> new IllegalStateException("Cannot find shape " + shapeId));
        return switch (shape.getType()) {
            case LIST -> ParameterizedTypeName.get(
                    ClassName.get(List.class),
                    typeForShapeNoEnum(shape.asListShape().get().getMember().getTarget())
            );
            case SET -> ParameterizedTypeName.get(
                    ClassName.get(Set.class),
                    typeForShapeNoEnum(shape.asSetShape().get().getMember().getTarget())
            );
            default -> throw new IllegalStateException(
                    "typeForListOrSetNoEnum only accepts LIST or SET. Got: " + shape.getType()
                            + " for ShapeId: " + shapeId);
        };
    }

    /**
     * <p>In the AWS SDK Java V1,
     * structures never return Enums, only their string representation.
     * Thus, any methods that handle the result of a get Enum value
     * must handle String, not the Enum reference.</p>
     *
     * <p>At this time, we believe that is only needs to be called
     * for aggregates other than structure or union,
     * as only Aggregate converters will indirectly deal with enums.</p>
     *
     * <p>Any direct involvement with Enums are safe,
     * since we overload the enum converter methods.</p>
     **/
    public TypeName typeForShapeNoEnum(ShapeId shapeId) {
        final Shape shape = model.expectShape(shapeId);
        if (shape.hasTrait(EnumTrait.class)) {
            return classForString();
        }
        if (SHAPE_TYPES_LIST_SET.contains(shape.getType())) {
            return typeForListOrSetNoEnum(shapeId);
        }
        return typeForShape(shapeId);
    }

    @SuppressWarnings("OptionalGetWithoutIsPresent")
    public TypeName typeForListOrSetMember(ShapeId shapeId) {
        Shape shape = model.expectShape(shapeId);
        return switch (shape.getType()) {
            case MEMBER -> typeForShape(shape.getId());
            case LIST -> typeForShape(shape.asListShape().get().getMember().getTarget());
            case SET -> typeForShape(shape.asSetShape().get().getMember().getTarget());
            default -> throw new IllegalStateException(
                    "typeForListOrSetMember only accepts MEMBER, LIST, or SET. Got: " + shape.getType());
        };
    }

    public ClassName typeForStructure(StructureShape shape) {
        //TODO handle traits on structures
        if (isInServiceNameSpace(shape.getId())) {
            return ClassName.get(modelPackage, shape.getId().getName());
        }
        // Assume that structure is in the package's root;
        // This is a VERY BOLD assumption.
        return ClassName.get(
                shape.getId().getNamespace(),
                StringUtils.capitalize(shape.getId().getName()));
    }

    public ClassName typeForService(ServiceShape shape) {
        throw new UnsupportedOperationException("Not yet implemented for not AWS-SDK Style");
    }

    @SuppressWarnings("unused")
    public ClassName typeForResource(ResourceShape shape) {
        throw new UnsupportedOperationException("Not yet implemented for not AWS-SDK Style");
    }

    public TypeName typeForOperationOutput(ShapeId outputShapeId) {
        throw new UnsupportedOperationException("Not yet implemented for not AWS-SDK Style");
    }

    public TypeName baseErrorForService() {
        throw new UnsupportedOperationException("Not yet implemented for not AWS-SDK Style");
    }
}
