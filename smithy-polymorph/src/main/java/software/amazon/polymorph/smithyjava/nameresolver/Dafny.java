package software.amazon.polymorph.smithyjava.nameresolver;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.ParameterizedTypeName;
import com.squareup.javapoet.TypeName;
import com.squareup.javapoet.WildcardTypeName;

import java.math.BigDecimal;
import java.math.BigInteger;

import dafny.DafnyMap;
import dafny.DafnySequence;
import dafny.DafnySet;
import dafny.Tuple0;
import software.amazon.polymorph.utils.DafnyNameResolverHelpers;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
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

import static software.amazon.polymorph.smithyjava.generator.Generator.Constants.SUPPORTED_CONVERSION_AGGREGATE_SHAPES;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.SMITHY_API_UNIT;
import static software.amazon.smithy.utils.StringUtils.capitalize;

/**
 * Provides a consistent mapping between names of
 * model Shapes and generated identifiers in Java
 * for the Dafny generated Java code.
 */
public class Dafny extends NameResolver {

    public Dafny(
            final String packageName,
            final Model model,
            final ServiceShape serviceShape
    ) {
        super(
                packageName,
                serviceShape,
                model,
                modelPackageNameForServiceShape(serviceShape)
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

    public static String enumIsName(String name) {
        String dafnyEnumName = enumFormatter(name);
        return "is_" + dafnyEnumName;
    }

    public static String aggregateSizeMethod(ShapeType shapeType) {
        return switch (shapeType) {
            case LIST -> "length()";
            case SET, MAP -> "size();";
            default -> throw new IllegalStateException(
                    "aggregateSizeMethod only accepts LIST, SET, or MAP. Got : " + shapeType);
        };
    }

    static String modelPackageNameForNamespace(final String namespace) {
        return DafnyNameResolverHelpers.packageNameForNamespace(namespace) + ".Types";
    }

    static String packageNameForServiceShape(ServiceShape serviceShape) {
        return DafnyNameResolverHelpers.packageNameForNamespace(serviceShape.getId().getNamespace());
    }

    static String modelPackageNameForServiceShape(ServiceShape serviceShape) {
        return modelPackageNameForNamespace(serviceShape.getId().getNamespace());
    }

    public static CodeBlock getMemberField(MemberShape shape) {
        return CodeBlock.of("_$L", capitalize(shape.getMemberName()));
    }

    public static CodeBlock getMemberFieldValue(MemberShape shape) {
        // if required, get via Field
        if (shape.isRequired()) {
            return getMemberField(shape);
        }
        // if optional, get via dtor_value()
        return CodeBlock.of("$L.dtor_value()", getMemberField(shape));
    }

    public String packageName() {
        return this.packageName;
    }

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
            case TIMESTAMP -> typeForCharacterSequence();
            case BYTE -> TypeName.BYTE.box();
            case SHORT -> TypeName.SHORT.box();
            case INTEGER -> TypeName.INT.box();
            case LONG -> TypeName.LONG.box();
            case BIG_DECIMAL -> ClassName.get(BigDecimal.class);
            case BIG_INTEGER -> ClassName.get(BigInteger.class);
            case LIST, SET, MAP -> typeForAggregateWithWildcard(shapeId);
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

    public ClassName getDafnyAbstractServiceError() {
        return ClassName.get(modelPackage, "Error");
    }

    public ClassName getDafnyOpaqueServiceError() {
        return ClassName.get(modelPackage, "Error_Opaque");
    }

    // Because we want a ClassName instead of a TypeName
    // This needs to be public.
    public ClassName classForShape(Shape shape) {
        return classForShape(shape.toShapeId());
    }

    public ClassName classForShape(ShapeId shapeId) {
        // Assume class will be in model package
        // i.e.: Dafny.<Namespace>.Types.Shape
        return ClassName.get(
                modelPackageNameForNamespace(shapeId.getNamespace()),
                StringUtils.capitalize(shapeId.getName())
        );
    }

    TypeName typeForString(StringShape shape) {
        if (!shape.hasTrait(EnumTrait.class)) {
            return typeForCharacterSequence();
        }
        return classForShape(shape);
    }

    TypeName typeForCharacterSequence() {
        return ParameterizedTypeName.get(
                ClassName.get(DafnySequence.class),
                WildcardTypeName.subtypeOf(Character.class)
        );
    }

    ClassName typeForStructure(StructureShape shape) {
        if (shape.hasTrait(ErrorTrait.class)) {
            return typeForError(shape);
        }
        if (shape.getId().equals(SMITHY_API_UNIT)) {
            return ClassName.get(Tuple0.class);
        }
        return classForShape(shape);
    }

    ClassName typeForError(Shape shape) {
        // AwsCryptographicMaterialProvidersException -> Error_AwsCryptographicMaterialProvidersException
        ClassName className = classForShape(shape);
        return ClassName.get(className.packageName(), "Error_" + className.simpleName());
    }

    TypeName typeForService(ServiceShape shape) {
        throw new UnsupportedOperationException("Not yet implemented for not AWS-SDK Style");
    }

    TypeName typeForResource(ResourceShape shape) {
        throw new UnsupportedOperationException("Not yet implemented for not AWS-SDK Style");
    }
}
