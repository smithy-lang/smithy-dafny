package software.amazon.polymorph.smithyjava.nameresolver;

import com.google.common.base.Joiner;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.ParameterizedTypeName;
import com.squareup.javapoet.TypeName;
import com.squareup.javapoet.WildcardTypeName;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Arrays;
import java.util.Set;
import java.util.stream.Stream;

import dafny.DafnyMap;
import dafny.DafnySequence;
import dafny.DafnySet;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ShapeType;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.utils.StringUtils;

import static software.amazon.polymorph.smithyjava.generator.awssdk.Generator.Constants.SUPPORTED_CONVERSION_AGGREGATE_SHAPES;

/**
 * Provides a consistent mapping between names of
 * model Shapes and generated identifiers in Java
 * for the Dafny generated Java code.
 */
public class Dafny {
    protected final String packageName;
    protected final Model model;
    protected final ServiceShape serviceShape;
    protected final String modelPackage;

    public Dafny(
            final String packageName,
            final ServiceShape serviceShape,
            final Model model
    ) {
        this.packageName = packageName;
        this.model = model;
        this.serviceShape = serviceShape;
        this.modelPackage = modelPackageNameForServiceShape(serviceShape);
    }

    public String packageName() { return this.packageName; }

    /**
     * Returns the Dafny-compiled-Java type corresponding to the given shape.
     * <p>
     */
    @SuppressWarnings("OptionalGetWithoutIsPresent")
    public TypeName typeForShape(final ShapeId shapeId) {
        final Shape shape = model.getShape(shapeId)
                .orElseThrow(() -> new IllegalStateException("Cannot find shape " + shapeId));
        return switch (shape.getType()) {
            case BLOB -> ParameterizedTypeName.get(
                    ClassName.get(DafnySequence.class),
                    WildcardTypeName.subtypeOf(TypeName.BYTE.box())
            );
            case BOOLEAN -> TypeName.BOOLEAN.box();
            case STRING -> typeForString(shape.asStringShape().get());
            case TIMESTAMP -> ParameterizedTypeName.get(
                    ClassName.get(DafnySequence.class),
                    ClassName.get(Character.class)
            );
            case BYTE -> TypeName.BYTE.box();
            case SHORT -> TypeName.SHORT.box();
            case INTEGER -> TypeName.INT.box();
            case LONG -> TypeName.LONG.box();
            case BIG_DECIMAL -> ClassName.get(BigDecimal.class);
            case BIG_INTEGER -> ClassName.get(BigInteger.class);
            case LIST -> ParameterizedTypeName.get(
                    ClassName.get(DafnySequence.class),
                    typeForShape(shape.asListShape().get().getMember().getTarget())
            );
            case SET -> ParameterizedTypeName.get(
                    ClassName.get(DafnySet.class),
                    typeForShape(shape.asSetShape().get().getMember().getTarget())
            );
            case MAP -> ParameterizedTypeName.get(
                    ClassName.get(DafnyMap.class),
                    typeForShape(shape.asMapShape().get().getKey().getTarget()),
                    typeForShape(shape.asMapShape().get().getValue().getTarget())
            );
            case MEMBER -> typeForShape(shape.asMemberShape().get().getTarget());
            case STRUCTURE -> typeForStructure(shape.asStructureShape().get());
            case SERVICE -> typeForService(shape.asServiceShape().get());
            case RESOURCE -> typeForResource(shape.asResourceShape().get());
            /* TODO: Handle Unions
            case UNION -> dafnyTypeForUnion(shape.asUnionShape().get());
            */
            default -> throw new UnsupportedOperationException("Unsupported shape " + shapeId);
        };
    }

    @SuppressWarnings("OptionalGetWithoutIsPresent")
    public TypeName typeForAggregateWithWildcard(final ShapeId shapeId) {
        final Shape shape = model.getShape(shapeId)
                .orElseThrow(() -> new IllegalStateException("Cannot find shape " + shapeId));

        if (!SUPPORTED_CONVERSION_AGGREGATE_SHAPES.contains(shape.getType())) {
            throw new UnsupportedOperationException(
                    "No Dafny Java Type for %s yet.".formatted(shape.getType())
            );
        }
        return switch (shape.getType()) {
            case LIST -> ParameterizedTypeName.get(
                    ClassName.get(DafnySequence.class),
                    WildcardTypeName.subtypeOf(typeForShape(shape.asListShape().get().getMember().getTarget()))
            );
            case SET -> ParameterizedTypeName.get(
                    ClassName.get(DafnySet.class),
                    WildcardTypeName.subtypeOf(typeForShape(shape.asSetShape().get().getMember().getTarget()))
            );
            case MAP -> ParameterizedTypeName.get(
                    ClassName.get(DafnyMap.class),
                    WildcardTypeName.subtypeOf(typeForShape(shape.asMapShape().get().getKey().getTarget())),
                    WildcardTypeName.subtypeOf(typeForShape(shape.asMapShape().get().getValue().getTarget()))
            );
            default -> throw new IllegalStateException("Unexpected value: " + shape.getType());
        };
    }

    public TypeName getDafnyAbstractServiceError() {
        return ClassName.get(modelPackage, "Error");
    }

    // Because we want a ClassName instead of a TypeName
    // This needs to be public.
    public ClassName classForShape(Shape shape) {
        return classForShape(shape.toShapeId());
    }

    public ClassName classForShape(ShapeId shapeId) {
        return ClassName.get(
                modelPackage,
                StringUtils.capitalize(shapeId.getName())
        );
    }

    /**
     * Dafny generated Java enums replace '_' with '__'.
     * ex: SYMMETRIC_DEFAULT -> SYMMETRIC__DEFAULT
     */
    public static String enumFormatter(String name) {
        return name.replace("_", "__");
    }

    public static String enumCreate(String name) {
        String dafnyEnumName = enumFormatter(name);
        return "create_" + dafnyEnumName;
    }

    public static final Set<ShapeType> UNSUPPORTED_SHAPES;
    static {
        UNSUPPORTED_SHAPES = Set.of(
                ShapeType.FLOAT, ShapeType.DOUBLE, ShapeType.DOCUMENT, ShapeType.UNION
        );
    }

    TypeName typeForString(StringShape shape) {
        if (!shape.hasTrait(EnumTrait.class)) {
            return ParameterizedTypeName.get(
                    ClassName.get(DafnySequence.class),
                    WildcardTypeName.subtypeOf(Character.class)
            );
        }
        return classForShape(shape);
    }

    ClassName typeForStructure(StructureShape shape) {
        if (shape.hasTrait(ErrorTrait.class)) {
            return typeForError(shape);
        }
        return classForShape(shape);
    }

    ClassName typeForError(Shape shape) {
        // AwsCryptographicMaterialProvidersException -> Error_AwsCryptographicMaterialProvidersException
        ClassName className = classForShape(shape);
        return ClassName.get(className.packageName(), "Error_" + className.simpleName());
    }

    TypeName typeForService(ServiceShape shape) {
        throw new UnsupportedOperationException("Not yet implemented for generic");
    }

    TypeName typeForResource(ResourceShape shape) {
        throw new UnsupportedOperationException("Not yet implemented for generic");
    }

    // TODO: replace with method from DafnyNameResolver
    static String packageNameForNamespace(final String namespace) {
        final Stream<String> namespaceParts = Arrays
                .stream(namespace.split("\\."))
                .map(StringUtils::capitalize);
        return "Dafny." + Joiner.on('.').join(namespaceParts.iterator());
    }

    // TODO: replace with method from DafnyNameResolver
    static String modelPackageNameForNamespace(final String namespace) {
        return packageNameForNamespace(namespace) + ".Types";
    }

    static String packageNameForServiceShape(ServiceShape serviceShape) {
        return packageNameForNamespace(serviceShape.getId().getNamespace());
    }

    static String modelPackageNameForServiceShape(ServiceShape serviceShape) {
        return modelPackageNameForNamespace(serviceShape.getId().getNamespace());
    }
}
