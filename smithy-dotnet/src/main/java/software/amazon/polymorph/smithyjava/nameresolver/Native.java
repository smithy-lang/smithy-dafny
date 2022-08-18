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
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.BoxTrait;


/**
 * Provides a consistent mapping between names of
 * model Shapes and generated identifiers in Java
 * for the native Java code.
 */
public class Native {
    protected final String packageName;
    protected final Model model;
    protected final ServiceShape serviceShape;

    public Native(
            final String packageName,
            final ServiceShape serviceShape,
            final Model model
    ) {
        this.packageName = packageName;
        this.model = model;
        this.serviceShape = serviceShape;
    }


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
                Map.entry(ShapeType.STRING, ClassName.get(String.class)),
                Map.entry(ShapeType.BYTE, TypeName.BYTE),
                Map.entry(ShapeType.SHORT, TypeName.SHORT),
                Map.entry(ShapeType.INTEGER, TypeName.INT),
                Map.entry(ShapeType.LONG, TypeName.LONG),
                Map.entry(ShapeType.FLOAT, TypeName.FLOAT),
                Map.entry(ShapeType.DOUBLE, TypeName.DOUBLE),
                Map.entry(ShapeType.TIMESTAMP, ClassName.get(Date.class)),
                Map.entry(ShapeType.BIG_DECIMAL, ClassName.get(BigDecimal.class)),
                Map.entry(ShapeType.BIG_INTEGER, ClassName.get(BigInteger.class))
        );
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
            case BLOB, STRING, TIMESTAMP, BIG_DECIMAL, BIG_INTEGER -> NATIVE_TYPES_BY_SIMPLE_SHAPE_TYPE.get(shape.getType());
            case LIST -> ParameterizedTypeName.get(
                    ClassName.get(List.class),
                    typeForShape(shape.asListShape().get().getMember().getTarget())
            );
            case MAP -> ParameterizedTypeName.get(
                    ClassName.get(Map.class),
                    typeForShape(shape.asMapShape().get().getKey().getTarget()),
                    typeForShape(shape.asMapShape().get().getValue().getTarget())
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

    public static final Set<ShapeType> UNSUPPORTED_SHAPES;
    static {
        UNSUPPORTED_SHAPES = Set.of(
                ShapeType.DOCUMENT, ShapeType.UNION
        );
    }

    public TypeName typeForStructure(StructureShape shape) {
        throw new UnsupportedOperationException("Not yet implemented for generic");
    }

    public TypeName typeForService(ServiceShape shape) {
        throw new UnsupportedOperationException("Not yet implemented for generic");
    }

    public TypeName typeForResource(ResourceShape shape) {
        throw new UnsupportedOperationException("Not yet implemented for generic");
    }
}
