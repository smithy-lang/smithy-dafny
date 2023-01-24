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
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.traits.ReferenceTrait;

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

import static software.amazon.polymorph.utils.AwsSdkNameResolverHelpers.isInAwsSdkNamespace;
import static software.amazon.polymorph.smithyjava.generator.Generator.Constants.SUPPORTED_CONVERSION_AGGREGATE_SHAPES;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.DAFNY_RESULT_CLASS_NAME;
import static software.amazon.polymorph.smithyjava.nameresolver.Constants.SMITHY_API_UNIT;
import static software.amazon.polymorph.utils.DafnyNameResolverHelpers.dafnyCompilesExtra_;
import static software.amazon.polymorph.utils.DafnyNameResolverHelpers.dafnyExternNamespaceForShapeId;
import static software.amazon.polymorph.utils.DafnyNameResolverHelpers.packageNameForNamespace;
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

    /**
     * @param name A Constructor of the Dafny Datatype.
     * @param isRecordType Does the datatype have a single data constructor,
     *                     also called a "record type"?
     * @return The name of Dafny-Java created method to create an instance of
     * the constructor.
     */
    public static String datatypeConstructorCreate(String name, boolean isRecordType) {
        if (isRecordType) {
            return "create";
        }
        return "create_" + dafnyCompilesExtra_(name);
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
            case BLOB -> Dafny.typeForBlob();
            case BOOLEAN -> TypeName.BOOLEAN.box();
            case STRING -> typeForString(shape.asStringShape().get());
            case TIMESTAMP -> typeForCharacterSequence();
            case BYTE -> TypeName.BYTE.box();
            case SHORT -> TypeName.SHORT.box();
            case INTEGER -> TypeName.INT.box();
            case LONG -> TypeName.LONG.box();
            case DOUBLE -> Dafny.typeForDouble();
            case BIG_DECIMAL -> ClassName.get(BigDecimal.class);
            case BIG_INTEGER -> ClassName.get(BigInteger.class);
            case LIST, SET, MAP -> typeForAggregateWithWildcard(shapeId);
            case MEMBER -> typeForShape(shape.asMemberShape().get().getTarget());
            case STRUCTURE -> classForStructure(shape.asStructureShape().get());
            case SERVICE -> classNameForService(shape.asServiceShape().get());
            case RESOURCE -> classNameForResource(shape.asResourceShape().get());
            // Unions are identical to Structures (in this context).
            case UNION -> classForNotErrorNotUnitShape(shape.asUnionShape().get());
            default -> throw new UnsupportedOperationException("Unsupported shape " + shapeId);
        };
    }

    private static TypeName typeForBlob() {
        return ParameterizedTypeName.get(
                ClassName.get(DafnySequence.class),
                WildcardTypeName.subtypeOf(TypeName.BYTE.box()));
    }

    static TypeName typeForDouble() {
        return typeForBlob();
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
        if (shape.hasTrait(ReferenceTrait.class)) {
            // It is safe to use typeForShape here, as ReferenceTrait will always turn into a Resource or Service
            TypeName interfaceClassName = typeForShape(shapeId);
            return  CodeBlock.of("$T.reference($T.class)", TypeDescriptor.class, interfaceClassName);
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
        if (shape.hasTrait(EnumTrait.class)) {
            return classForNotErrorNotUnitShape(shape);
        }
        // If the shape has the dafnyUtf8Bytes trait,
        // the dafny representation will use Bytes
        if (shape.hasTrait(DafnyUtf8BytesTrait.class)) {
            return Dafny.typeForBlob();
        }
        return typeForCharacterSequence();
    }

    TypeName typeForCharacterSequence() {
        return ParameterizedTypeName.get(
                ClassName.get(DafnySequence.class),
                WildcardTypeName.subtypeOf(Character.class)
        );
    }

    public TypeName classForStructure(StructureShape shape) {
        if (shape.hasTrait(ErrorTrait.class)) {
            return classForError(shape);
        }
        if (shape.hasTrait(ReferenceTrait.class)) {
            return typeForShape(shape.expectTrait(ReferenceTrait.class).getReferentId());
        }
        if (shape.getId().equals(SMITHY_API_UNIT)) {
            return ClassName.get(Tuple0.class);
        }
        return classForNotErrorNotUnitShape(shape);
    }

    public ClassName classForError(Shape shape) {
        if (!shape.hasTrait(ErrorTrait.class)) {
            throw new IllegalArgumentException("shape MUST have ErrorTrait. ShapeId: %s".formatted(shape.getId()));
        }
        // AwsCryptographicMaterialProvidersException -> Error_AwsCryptographicMaterialProvidersException
        ClassName className = classForNotErrorNotUnitShape(shape);
        return ClassName.get(className.packageName(), "Error_" + dafnyCompilesExtra_(className.simpleName()));
    }

    /** @return The interface for a service client. */
    // This facilitates an override by a subclass
     ClassName classNameForService(final ServiceShape shape) {
        return interfaceForService(shape);
    }

     /** @return The interface for a service client.*/
    public static ClassName interfaceForService(final ServiceShape shape) {
        final String packageName = dafnyExternNamespaceForShapeId(shape.getId());
        final String interfaceName = DafnyNameResolver.traitNameForServiceClient(shape);
        return ClassName.get(packageName, dafnyCompilesExtra_(interfaceName));
    }

    /** @return The concrete class for a service client. */
    public ClassName classNameForConcreteServiceClient(ServiceShape shape) {
        String packageName = packageNameForNamespace(shape.getId().getNamespace());
        String concreteClass = DafnyNameResolver.classNameForServiceClient(shape);
        return ClassName.get(packageName, dafnyCompilesExtra_(concreteClass));
    }

    public ClassName classNameForNamespaceDefault() {
        String packageName = packageNameForNamespace(this.serviceShape.getId().getNamespace());
        return ClassName.get(packageName, "__default");
    }

    /** @return The interface for a resource.*/
    // This facilitates an override by a subclass
    ClassName classNameForResource(final ResourceShape shape) {
        return Dafny.interfaceForResource(shape);
    }

    /** @return The interface for a resource.*/
    public static ClassName interfaceForResource(final ResourceShape shape) {
        final String packageName = dafnyExternNamespaceForShapeId(shape.getId());
        final String interfaceName = DafnyNameResolver.traitNameForResource(shape);
        return ClassName.get(packageName, dafnyCompilesExtra_(interfaceName));
    }

    public ClassName classNameForInterface(Shape shape) {
        // if shape is an AWS Service/Resource, return Dafny Types Interface
        if (isInAwsSdkNamespace(shape.toShapeId())) {
            if (shape.isServiceShape()) {
                // TODO: use AwsSdkDafnyV2 is AWS SDK v2 flag is present
                //noinspection OptionalGetWithoutIsPresent
                return AwsSdkDafnyV1.classNameForAwsService(shape.asServiceShape().get());
            }
            if (shape.isResourceShape()) {
                // TODO: use AwsSdkDafnyV2 is AWS SDK v2 flag is present
                //noinspection OptionalGetWithoutIsPresent
                return AwsSdkDafnyV1.classNameForAwsResource(shape.asResourceShape().get());
            }
        }
        // if operation takes a non-AWS Service/Resource, return Dafny Interface Or Local Service
        if (shape.isResourceShape()) {
            //noinspection OptionalGetWithoutIsPresent
            return interfaceForResource(shape.asResourceShape().get());
        }
        if (shape.isServiceShape()) {
            //noinspection OptionalGetWithoutIsPresent
            return interfaceForService(shape.asServiceShape().get());
        }
        throw new IllegalArgumentException(
                "Polymorph only supports interfaces for Service & Resource Shapes. ShapeId: %s"
                        .formatted(shape.toShapeId()));
    }
}
