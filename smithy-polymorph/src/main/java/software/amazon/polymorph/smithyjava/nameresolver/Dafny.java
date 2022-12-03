package software.amazon.polymorph.smithyjava.nameresolver;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.ParameterizedTypeName;
import com.squareup.javapoet.TypeName;
import com.squareup.javapoet.WildcardTypeName;


import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.Map;
import java.util.Objects;

import javax.annotation.Nullable;

import dafny.DafnyMap;
import dafny.DafnySequence;
import dafny.DafnySet;
import dafny.Tuple0;
import dafny.TypeDescriptor;
import software.amazon.polymorph.smithydafny.DafnyNameResolver;
import software.amazon.polymorph.smithyjava.MethodReference;
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

import static software.amazon.polymorph.smithyjava.generator.Generator.Constants.SUPPORTED_CONVERSION_AGGREGATE_SHAPES;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.DAFNY_RESULT_CLASS_NAME;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.SMITHY_API_UNIT;
import static software.amazon.polymorph.utils.DafnyNameResolverHelpers.dafnyCompilesExtra_;
import static software.amazon.polymorph.utils.DafnyNameResolverHelpers.dafnyExternNamespaceForShapeId;
import static software.amazon.polymorph.utils.DafnyNameResolverHelpers.packageNameForNamespace;
import static software.amazon.polymorph.utils.ModelUtils.isSmithyApiShape;
import static software.amazon.smithy.utils.StringUtils.capitalize;

/**
 * Provides a consistent mapping between names of
 * model Shapes and generated identifiers in Java
 * for the Dafny generated Java code.
 */
public class Dafny extends NameResolver {
    private static final Logger LOGGER = LoggerFactory.getLogger(Dafny.class);
    protected static final Map<ShapeType, CodeBlock> TYPE_DESCRIPTOR_BY_SHAPE_TYPE;
    static {
        TYPE_DESCRIPTOR_BY_SHAPE_TYPE = Map.ofEntries(
                Map.entry(ShapeType.STRING, CodeBlock.of("$T._typeDescriptor($T.CHAR)", DafnySequence.class, TypeDescriptor.class)),
                // Tony is not sure BLOB is correct...
                Map.entry(ShapeType.BLOB, CodeBlock.of("$T._typeDescriptor($T.BYTE)", DafnySequence.class, TypeDescriptor.class)),
                Map.entry(ShapeType.BOOLEAN, CodeBlock.of("$T.BOOLEAN", TypeDescriptor.class)),
                Map.entry(ShapeType.BYTE, CodeBlock.of("$T.BYTE", TypeDescriptor.class)),
                Map.entry(ShapeType.SHORT, CodeBlock.of("$T.SHORT", TypeDescriptor.class)),
                Map.entry(ShapeType.INTEGER, CodeBlock.of("$T.INT", TypeDescriptor.class)),
                Map.entry(ShapeType.LONG, CodeBlock.of("$T.LONG", TypeDescriptor.class)),
                Map.entry(ShapeType.TIMESTAMP, CodeBlock.of("$T._typeDescriptor($T.CHAR)", DafnySequence.class, TypeDescriptor.class)),
                Map.entry(ShapeType.BIG_INTEGER, CodeBlock.of("$T.BIG_INTEGER", TypeDescriptor.class))
        );
    }

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

    public static String datatypeConstructorCreate(String name) {
        String dafnyEnumName = dafnyCompilesExtra_(name);
        return "create_" + dafnyEnumName;
    }

    public static String datatypeConstructorIs(String name) {
        String dafnyEnumName = dafnyCompilesExtra_(name);
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
        return packageNameForNamespace(namespace) + ".Types";
    }

    static String packageNameForServiceShape(ServiceShape serviceShape) {
        return packageNameForNamespace(serviceShape.getId().getNamespace());
    }

    static String modelPackageNameForServiceShape(ServiceShape serviceShape) {
        return modelPackageNameForNamespace(serviceShape.getId().getNamespace());
    }

    public static CodeBlock getMemberField(MemberShape shape) {
        return CodeBlock.of("dtor_$L()", dafnyCompilesExtra_(shape.getMemberName()));
    }

    /** If not optional, get via {@code dtor_<memberName>()}.
     * Otherwise, get via {@code dtor_<memberName>().dtor_value()}*/
    public static CodeBlock getMemberFieldValue(MemberShape shape) {
        // if required, get via Field
        if (shape.isRequired()) {
            return getMemberField(shape);
        }
        // if optional, get via dtor_value()
        return CodeBlock.of("$L.dtor_value()", getMemberField(shape));
    }

    public static TypeName asDafnyResult(TypeName success, TypeName failure) {
        return ParameterizedTypeName.get(
                DAFNY_RESULT_CLASS_NAME,
                success,
                failure
        );
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
            case STRUCTURE -> classForStructure(shape.asStructureShape().get());
            case SERVICE -> typeForService(shape.asServiceShape().get());
            case RESOURCE -> typeForResource(shape.asResourceShape().get());
            // Unions are identical to Structures (in this context).
            case UNION -> classForNotErrorNotUnitShape(shape.asUnionShape().get());
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

    public ClassName abstractClassForError() {
        return ClassName.get(modelPackage, "Error");
    }

    public ClassName classForOpaqueError() {
        return classForDatatypeConstructor("Error", "Opaque");
    }

    public CodeBlock typeDescriptor(ShapeId shapeId) {
        Shape shape = model.getShape(shapeId)
                .orElseThrow(() -> new IllegalStateException("Cannot find shape " + shapeId));
        if (shape.isMemberShape()) {
            // We have just established it is a member shape, asMemberShape will return a value
            //noinspection OptionalGetWithoutIsPresent
            return typeDescriptor(shape.asMemberShape().get().getTarget());
        }
        if (shape.hasTrait(ErrorTrait.class)) {
            return CodeBlock.of("$L()",
                    new MethodReference(abstractClassForError(), "_typeDescriptor").asNormalReference());
        }
        if (shape.getId().equals(SMITHY_API_UNIT)) {
            return CodeBlock.of("$L()",
                    new MethodReference(ClassName.get(Tuple0.class), "_typeDescriptor").asNormalReference());
        }
        if (shape.getType().getCategory().equals(ShapeType.Category.SIMPLE) && !shape.hasTrait(EnumTrait.class)) {
            @Nullable CodeBlock typeDescriptor = TYPE_DESCRIPTOR_BY_SHAPE_TYPE.get(shape.getType());
            if (Objects.nonNull(typeDescriptor)) {
                return CodeBlock.of("$L", typeDescriptor);
            }
        }
        return CodeBlock.of("$L()",
                new MethodReference(classForNotErrorNotUnitShape(shape), "_typeDescriptor").asNormalReference());
    }

    /*
    For Datatypes, the destructor (thing) is the left Hand ,
    and the constructors (x, y) are the right hand of:
    datatype thing = x | y

    Outside the Dafny world,
    Datatype constructors are sometimes called variants.
    */
    public ClassName classForDatatypeConstructor(String dataTypeName, String constructorName) {
        return ClassName.get(modelPackage, "%s_%s".formatted(
                dafnyCompilesExtra_(dataTypeName), dafnyCompilesExtra_(constructorName)));
    }

    // This method assumes the shape is not an Error nor a Unit
    ClassName classForNotErrorNotUnitShape(Shape shape) {
        return classForNotErrorNotUnitShape(shape.toShapeId());
    }

    // This method assumes the shape is not an Error nor a Unit
    ClassName classForNotErrorNotUnitShape(ShapeId shapeId) {
        // Assume class will be in model package
        // i.e.: Dafny.<Namespace>.Types.Shape
        // And that Shape is not an Error
        return ClassName.get(
                modelPackageNameForNamespace(shapeId.getNamespace()),
                dafnyCompilesExtra_(capitalize(shapeId.getName()))
        );
    }

    TypeName typeForString(StringShape shape) {
        if (!shape.hasTrait(EnumTrait.class)) {
            return typeForCharacterSequence();
        }
        return classForNotErrorNotUnitShape(shape);
    }

    TypeName typeForCharacterSequence() {
        return ParameterizedTypeName.get(
                ClassName.get(DafnySequence.class),
                WildcardTypeName.subtypeOf(Character.class)
        );
    }

    public ClassName classForStructure(StructureShape shape) {
        if (shape.hasTrait(ErrorTrait.class)) {
            return classForError(shape);
        }
        if (shape.getId().equals(SMITHY_API_UNIT)) {
            return ClassName.get(Tuple0.class);
        }
        return classForNotErrorNotUnitShape(shape);
    }

    ClassName classForError(Shape shape) {
        // AwsCryptographicMaterialProvidersException -> Error_AwsCryptographicMaterialProvidersException
        ClassName className = classForNotErrorNotUnitShape(shape);
        return ClassName.get(className.packageName(), "Error_" + dafnyCompilesExtra_(className.simpleName()));
    }

    /** @return The interface for a service client. */
     TypeName typeForService(ServiceShape shape) {
        String packageName = dafnyExternNamespaceForShapeId(shape.getId());
        String interfaceName = DafnyNameResolver.traitNameForServiceClient(shape);
        return ClassName.get(packageName, interfaceName);
    }

    /** @return The concrete class for a service client. */
    public ClassName classNameForConcreteServiceClient(ServiceShape shape) {
        String packageName = packageNameForNamespace(shape.getId().getNamespace());
        String concreteClass = DafnyNameResolver.classNameForServiceClient(shape);
        return ClassName.get(packageName, concreteClass);
    }

    public ClassName classNameForNamespaceDefault() {
        String packageName = packageNameForNamespace(this.serviceShape.getId().getNamespace());
        return ClassName.get(packageName, "__default");
    }

    TypeName typeForResource(ResourceShape shape) {
        throw new UnsupportedOperationException("Not yet implemented for not AWS-SDK Style");
    }
}
