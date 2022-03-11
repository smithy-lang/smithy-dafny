// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import com.google.common.annotations.VisibleForTesting;
import com.google.common.base.Joiner;
import com.google.common.base.Splitter;
import software.amazon.polymorph.smithydafny.DafnyNameResolver;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ListShape;
import software.amazon.smithy.model.shapes.MapShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.OperationShape;
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

import javax.annotation.Nullable;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Stream;

/**
 * Provides a consistent mapping between names of model Shapes and generated identifiers.
 */
public class DotNetNameResolver {
    private final Model model;
    private final ServiceShape serviceShape;

    public DotNetNameResolver(Model model, ServiceShape serviceShape) {
        this.model = model;
        this.serviceShape = serviceShape;
    }

    private static final Set<String> C_SHARP_BUILT_IN_VALUE_TYPES = Set.of(
            // integral numeric types
            "sbyte", "byte", "short", "ushort", "int", "uint", "long", "ulong", "nint", "nuint",
            // floating-point numeric types
            "float", "double", "decimal",
            // other primitives
            "bool", "char",
            // other non-primitive value types
            "System.DateTime"
    );

    public static final String TYPE_CONVERSION_CLASS_NAME = "TypeConversion";

    /**
     * Returns the C# namespace containing the C# implementation/interface for the given shape ID.
     */
    public String namespaceForShapeId(final ShapeId shapeId) {
        Stream<String> parts = Splitter.on('.')
                .splitToList(shapeId.getNamespace())
                .stream()
                .map(StringUtils::capitalize);
        return Joiner.on('.').join(parts.iterator());
    }

    public String namespaceForService() {
        return namespaceForShapeId(serviceShape.getId());
    }

    public String clientForService() {
        return serviceShape.getId().getName(serviceShape) + "Client";
    }

    public String baseClientForService() {
        return clientForService() + "Base";
    }

    public String interfaceForService() {
        return interfaceForService(serviceShape.getId());
    }

    public String interfaceForService(final ShapeId serviceShapeId) {
        return "I" + serviceShapeId.getName(serviceShape);
    }

    // TODO For the factory we want the name to match the modeled service name exactly.
    // Alternatively we could consider modelling the service name more generally and then appending "Factory",
    // however that might make the smithy model hard to understand if it isn't explicit that the service is a factory
    // via its name.
    public String staticFactoryForService() {
        return serviceShape.getId().getName(serviceShape);
    }

    public static String classForCommonServiceException(final ServiceShape serviceShape) {
        return "%sException".formatted(serviceShape.getId().getName(serviceShape));
    }

    public String classForCommonServiceException() {
        return DotNetNameResolver.classForCommonServiceException(serviceShape);
    }

    // TODO How to specify a specific top level exception that's different than the service name?
    // Do we need to specify via a new trait, or is there another approach?
    public static String classForCommonStaticFactoryException(final ServiceShape serviceShape) {
        if (serviceShape.getId().getName(serviceShape).equals("AwsEncryptionSdkFactory")) {
            return "AwsEncryptionSdkBaseException";
        } else if (serviceShape.getId().getName(serviceShape).equals("AwsCryptographicMaterialProvidersFactory")) {
            return "AwsCryptographicMaterialProvidersBaseException";
        }
        return "%sException".formatted(serviceShape.getId().getName(serviceShape));
    }

    public String classForCommonStaticFactoryException() {
        return DotNetNameResolver.classForCommonStaticFactoryException(serviceShape);
    }

    public String classForSpecificServiceException(final ShapeId structureShapeId) {
        final StructureShape shape = model.expectShape(structureShapeId, StructureShape.class);
        // Sanity check
        assert shape.hasTrait(ErrorTrait.class);
        return structureShapeId.getName(serviceShape);
    }

    public String methodForOperation(final ShapeId operationShapeId) {
        return model.expectShape(operationShapeId, OperationShape.class).getId().getName(serviceShape);
    }

    public String abstractMethodForOperation(final ShapeId operationShapeId) {
        return String.format("_%s", methodForOperation(operationShapeId));
    }

    /**
     * Returns the name of the class generated for the given structure shape. Note that this method is only valid for
     * structure shapes that will have a corresponding generated class.
     */
    public String classForStructure(final ShapeId structureShapeId) {
        final StructureShape structureShape = model.expectShape(structureShapeId, StructureShape.class);

        // Sanity check that we aren't using this method for non-generated structures
        assert !structureShape.hasTrait(ReferenceTrait.class);
        assert !structureShape.hasTrait(PositionalTrait.class);

        // Sanity check that we aren't using this method for generated error structures
        assert !structureShape.hasTrait(ErrorTrait.class);

        return model.expectShape(structureShapeId, StructureShape.class).getId().getName(serviceShape);
    }

    private static final Map<String, String> NATIVE_TYPES_BY_SMITHY_PRELUDE_SHAPE_NAME;
    private static final Map<ShapeType, String> NATIVE_TYPES_BY_SIMPLE_SHAPE_TYPE;

    static {
        NATIVE_TYPES_BY_SMITHY_PRELUDE_SHAPE_NAME = Map.ofEntries(
                Map.entry("String", "string"),
                Map.entry("Blob", "System.IO.MemoryStream"),
                Map.entry("Boolean", "bool"),
                Map.entry("PrimitiveBoolean", "bool"),
                Map.entry("Byte", "sbyte"),
                Map.entry("PrimitiveByte", "sbyte"),
                Map.entry("Short", "short"),
                Map.entry("PrimitiveShort", "short"),
                Map.entry("Integer", "int"),
                Map.entry("PrimitiveInteger", "int"),
                Map.entry("Long", "long"),
                Map.entry("PrimitiveLong", "long"),
                Map.entry("Float", "float"),
                Map.entry("PrimitiveFloat", "float"),
                Map.entry("Double", "double"),
                Map.entry("PrimitiveDouble", "double"),
                Map.entry("Timestamp", "System.DateTime")
        );
        NATIVE_TYPES_BY_SIMPLE_SHAPE_TYPE = Map.ofEntries(
                Map.entry(ShapeType.BLOB, "System.IO.MemoryStream"),
                Map.entry(ShapeType.BOOLEAN, "bool"),
                Map.entry(ShapeType.STRING, "string"),
                Map.entry(ShapeType.BYTE, "sbyte"),
                Map.entry(ShapeType.SHORT, "short"),
                Map.entry(ShapeType.INTEGER, "int"),
                Map.entry(ShapeType.LONG, "long"),
                Map.entry(ShapeType.FLOAT, "float"),
                Map.entry(ShapeType.DOUBLE, "double"),
                Map.entry(ShapeType.TIMESTAMP, "System.DateTime")
        );
    }

    /**
     * Returns the C# type used to store values of the given member shape within a structure class.
     * <p>
     * This is always nullable, so it can represent uninitialized values.
     */
    public String classFieldTypeForStructureMember(final MemberShape memberShape) {
        return nullableTypeForStructureMember(memberShape);
    }

    /**
     * Returns the C# type used to expose values of the given member shape as a property of its structure class.
     * <p>
     * This is always non-nullable.
     */
    public String classPropertyTypeForStructureMember(final MemberShape memberShape) {
        return baseTypeForShape(memberShape.getTarget());
    }

    protected String baseTypeForString(final StringShape stringShape) {
        final ShapeId shapeId = stringShape.getId();
        final String namespace = namespaceForShapeId(shapeId);
        return stringShape.hasTrait(EnumTrait.class)
                ? "%s.%s".formatted(namespace, classForEnum(shapeId))
                : "string";
    }

    protected String baseTypeForList(final ListShape listShape) {
        return "System.Collections.Generic.List<%s>".formatted(baseTypeForMember(listShape.getMember()));
    }

    protected String baseTypeForMap(final MapShape mapShape) {
        return "System.Collections.Generic.Dictionary<%s, %s>".formatted(
                baseTypeForMember(mapShape.getKey()),
                baseTypeForMember(mapShape.getValue()));
    }

    protected String baseTypeForStructure(final StructureShape structureShape) {
        // The base type of a reference structure is the base trait for its referent
        final Optional<ReferenceTrait> referenceTraitOptional = structureShape.getTrait(ReferenceTrait.class);
        if (referenceTraitOptional.isPresent()) {
            final ReferenceTrait referenceTrait = referenceTraitOptional.get();
            final ShapeId referentShapeId = referenceTrait.getReferentId();
            if (model.getShape(referentShapeId).isEmpty()) {
                // TODO: support external referents
                throw new IllegalStateException("Structure %s has external referent %s, this is unsupported"
                        .formatted(structureShape.getId(), referentShapeId));
            }
            return baseTypeForShape(referentShapeId);
        }

        // The base type of a positional structure is the base type of its sole member
        final Optional<ShapeId> positionalMember = ModelUtils.getPositionalStructureMember(structureShape);
        if (positionalMember.isPresent()) {
            return baseTypeForShape(positionalMember.get());
        }

        final String structureNamespace = namespaceForShapeId(structureShape.getId());

        // The base type of an error structure is the corresponding generated exception class
        if (structureShape.hasTrait(ErrorTrait.class)) {
            return "%s.%s".formatted(structureNamespace, classForSpecificServiceException(structureShape.getId()));
        }

        // The base type of any other structure is the name of the corresponding generated class
        return "%s.%s".formatted(structureNamespace, classForStructure(structureShape.getId()));
    }

    protected String baseTypeForMember(final MemberShape memberShape) {
        final String baseType = baseTypeForShape(memberShape.getTarget());
        final boolean isOptional = memberShapeIsOptional(memberShape);
        return isOptional ? baseTypeForOptionalMember(memberShape) : baseType;
    }

    protected String baseTypeForOptionalMember(final MemberShape memberShape) {
        final String baseType = baseTypeForShape(memberShape.getTarget());
        // We annotate C# value types with `?` to make them nullable.
        // We cannot do the same for C# reference types since those types are already nullable by design.
        // TODO: nullable reference types appear to be supported in C# 8.0+. Maybe revisit this.
        //  https://issues.amazon.com/issues/CrypTool-4156
        return isValueType(memberShape.getTarget()) ? baseType + "?" : baseType;
    }

    protected String baseTypeForService(final ServiceShape serviceShape) {
        final ShapeId shapeId = serviceShape.getId();

        // TODO better way to determine if AWS SDK
        if (shapeId.getNamespace().startsWith("com.amazonaws.")) {
            return new AwsSdkDotNetNameResolver(model, serviceShape).baseTypeForService(serviceShape);
        }

        return "%s.%s".formatted(
                namespaceForShapeId(shapeId), interfaceForService(shapeId));
    }

    protected String baseTypeForResource(final ResourceShape resourceShape) {
        final ShapeId shapeId = resourceShape.getId();
        return "%s.%s".formatted(
                namespaceForShapeId(shapeId), interfaceForResource(shapeId));
    }

    public boolean isValueType(final ShapeId shapeId) {
        final String baseType = baseTypeForShape(shapeId);
        return C_SHARP_BUILT_IN_VALUE_TYPES.contains(baseType);
    }

    @SuppressWarnings("OptionalGetWithoutIsPresent")
    public String baseTypeForShape(final ShapeId shapeId) {
        final Shape shape = model.expectShape(shapeId);

        // First check if this is a built-in Smithy shape. If so, we just map it to the native type and return
        if (ModelUtils.isSmithyApiShape(shapeId)) {
            @Nullable final String nativeTypeName = NATIVE_TYPES_BY_SMITHY_PRELUDE_SHAPE_NAME.get(shapeId.getName(serviceShape));
            return Objects.requireNonNull(nativeTypeName,
                    () -> String.format("No native type for prelude shape %s", shapeId));
        }

        return switch (shape.getType()) {
            // For supported simple shapes, just map to native types
            case BLOB, BOOLEAN, INTEGER, LONG, TIMESTAMP -> {
                @Nullable final String nativeTypeName = NATIVE_TYPES_BY_SIMPLE_SHAPE_TYPE.get(shape.getType());
                yield Objects.requireNonNull(nativeTypeName,
                        () -> String.format("No native type for shape type %s", shape.getType()));
            }

            case STRING -> baseTypeForString(shape.asStringShape().get());
            case LIST -> baseTypeForList(shape.asListShape().get());
            case MAP -> baseTypeForMap(shape.asMapShape().get());
            case STRUCTURE -> baseTypeForStructure(shape.asStructureShape().get());
            case MEMBER -> baseTypeForMember(shape.asMemberShape().get());
            case SERVICE -> baseTypeForService(shape.asServiceShape().get());
            case RESOURCE -> baseTypeForResource(shape.asResourceShape().get());

            default -> throw new UnsupportedOperationException("Shape %s has unsupported type %s"
                    .formatted(shapeId, shape.getType()));
        };
    }

    private String nullableTypeForStructureMember(final MemberShape memberShape) {
        return baseTypeForOptionalMember(memberShape);
    }

    /**
     * Returns the name of the (private) structure class field for the given member shape.
     */
    public String classFieldForStructureMember(final MemberShape memberShape) {
        return "_%s".formatted(StringUtils.uncapitalize(memberShape.getMemberName()));
    }

    /**
     * Returns the name of the (public) structure class property for the given member shape.
     */
    public String classPropertyForStructureMember(final MemberShape memberShape) {
        return StringUtils.capitalize(memberShape.getMemberName());
    }

    /**
     * Returns the name of the given member shape's IsSet method.
     */
    public String isSetMethodForStructureMember(final MemberShape memberShape) {
        return "IsSet%s".formatted(classPropertyForStructureMember(memberShape));
    }

    /**
     * Returns the name of the class property fur use as a variable name, i.e. the first letter is lower case
     */
    public String variableNameForClassProperty(final MemberShape memberShape) {
        String classProperty = StringUtils.capitalize(memberShape.getMemberName());
        return "var_%s%s".formatted(
                StringUtils.uncapitalize(classProperty.substring(0,1)),
                classProperty.substring(1));
    }

    public String interfaceForResource(final ShapeId resourceShapeId) {
        return String.format("I%s", StringUtils.capitalize(resourceShapeId.getName(serviceShape)));
    }

    public String baseClassForResource(final ShapeId resourceShapeId) {
        return String.format("%sBase", StringUtils.capitalize(resourceShapeId.getName(serviceShape)));
    }

    public String shimClassForResource(final ShapeId resourceShapeId) {
        return StringUtils.capitalize(resourceShapeId.getName(serviceShape));
    }

    public String classForEnum(final ShapeId enumShapeId) {
        return StringUtils.capitalize(enumShapeId.getName(serviceShape));
    }

    /**
     * Implements {@code DafnyAst.NonglobalVariable.CompilerizeName} for strings which are valid enum definition names
     * according to {@link ModelUtils#isValidEnumDefinitionName(String)}.
     *
     * @see <a href="https://github.com/dafny-lang/dafny/blob/319a1f8e6ac655ac10394a12c2140a9e09514115/Source/Dafny/AST/DafnyAst.cs#L5908}">CompilerizeName</a>
     */
    public static String dafnyCompiledNameForEnumDefinitionName(final String name) {
        if (!ModelUtils.isValidEnumDefinitionName(name)) {
            throw new IllegalArgumentException("The enum definition name '%s' is forbidden".formatted(name));
        }

        // We only allow uppercase ASCII letters and underscores in enum definition names, so it suffices to replace
        // each underscore with two underscores.
        return name.replace("_", "__");
    }

    /**
     * Returns a unique type converter method name for the given shape and type conversion direction.
     * <p>
     * This is necessary because all type converter methods for a given model will coexist in a single class. There is a
     * one-to-one mapping between shapes used in the model and type converters in the class, so the function that names
     * converter methods must also be one-to-one.
     */
    public static String typeConverterForShape(final ShapeId shapeId, final TypeConversionDirection direction) {
        final String encodedShapeId = encodedIdentForShapeId(shapeId);
        return String.format("%s_%s", direction.toString(), encodedShapeId);
    }

    /**
     * Returns the converter method name for the given shape and type conversion direction, qualified with the type
     * conversion class name.
     */
    public static String qualifiedTypeConverter(final ShapeId shapeId, final TypeConversionDirection direction) {
        final String methodName = DotNetNameResolver.typeConverterForShape(shapeId, direction);
        return "%s.%s".formatted(DotNetNameResolver.TYPE_CONVERSION_CLASS_NAME, methodName);
    }

    /**
     * Returns the type converter method name for the given service's common error shape and the given direction.
     */
    public static String typeConverterForCommonError(final ServiceShape serviceShape, final TypeConversionDirection direction) {
        return String.format("%s_CommonError_%s", direction.toString(), DotNetNameResolver.classForCommonStaticFactoryException(serviceShape));
    }

    /**
     * Like {@link DotNetNameResolver#typeConverterForCommonError(ServiceShape, TypeConversionDirection)}, but
     * qualified with the type conversion class name.
     */
    public static String qualifiedTypeConverterForCommonError(final ServiceShape serviceShape, final TypeConversionDirection direction) {
        final String methodName = DotNetNameResolver.typeConverterForCommonError(serviceShape, direction);
        return "%s.%s".formatted(DotNetNameResolver.TYPE_CONVERSION_CLASS_NAME, methodName);
    }

    /**
     * Returns the abstract Dafny-compiled-C# type corresponding to the given shape, or the concrete type if no such
     * abstract type exists. For example, a list shape is a {@code Dafny.ISequence} rather than a
     * {@code Dafny.Sequence}, but an integer shape is simply an {@code int}.
     * <p>
     * Note that this method is mutually recursive with the "dafnyTypeForA" methods (for aggregate shape types A), but
     * termination is guaranteed. This is because the Smithy specification requires that if an aggregate shape has a
     * path to itself (by recursively traversing through members and their targets), then the path must include a
     * structure or union shape (which have no type variables). The core Smithy validation logic takes responsibility to
     * ensure this.
     */
    @SuppressWarnings("OptionalGetWithoutIsPresent")
    public String dafnyTypeForShape(final ShapeId shapeId) {
        final Shape shape = model.getShape(shapeId)
                .orElseThrow(() -> new IllegalStateException("Cannot find shape " + shapeId));

        return switch (shape.getType()) {
            case BLOB -> "Dafny.ISequence<byte>";
            case BOOLEAN -> "bool";
            case STRING -> dafnyTypeForString(shape.asStringShape().get());
            case INTEGER -> "int";
            case LONG -> "long";
            // TODO create/use better timestamp type in Dafny libraries
            case TIMESTAMP -> "Dafny.ISequence<char>";
            case LIST -> dafnyTypeForList(shape.asListShape().get());
            case MAP -> dafnyTypeForMap(shape.asMapShape().get());
            case STRUCTURE -> dafnyTypeForStructure(shape.asStructureShape().get());
            case MEMBER -> dafnyTypeForMember(shape.asMemberShape().get());
            case SERVICE -> dafnyTypeForService(shape.asServiceShape().get());
            case RESOURCE -> dafnyTypeForResource(shape.asResourceShape().get());
            default -> throw new UnsupportedOperationException("Unsupported shape " + shapeId);
        };
    }

    public String dafnyConcreteTypeForEnum(final ShapeId shapeId) {
        return dafnyTypeForEnum(shapeId, true);
    }

    private String dafnyTypeForEnum(final ShapeId shapeId, final boolean concrete) {
        final String typePrefix = concrete ? "" : "_I";
        // We explicitly specify the Dafny namespace just in case of collisions.
        return "%s.%s%s".formatted(
                DafnyNameResolver.dafnyExternNamespaceForShapeId(shapeId),
                typePrefix,
                shapeId.getName(serviceShape));
    }

    private String dafnyTypeForString(final StringShape stringShape) {
        final ShapeId shapeId = stringShape.getId();
        if (stringShape.hasTrait(EnumTrait.class)) {
            return dafnyTypeForEnum(shapeId, false);
        }
        if (stringShape.hasTrait(DafnyUtf8BytesTrait.class)) {
            return "Dafny.ISequence<byte>";
        }
        return "Dafny.ISequence<char>";
    }

    private String dafnyTypeForList(final ListShape listShape) {
        return "Dafny.ISequence<%s>".formatted(dafnyTypeForMember(listShape.getMember()));
    }

    private String dafnyTypeForMap(final MapShape mapShape) {
        return "Dafny.IMap<%s, %s>".formatted(
                dafnyTypeForMember(mapShape.getKey()),
                dafnyTypeForMember(mapShape.getValue()));
    }

    private String dafnyTypeForStructure(final StructureShape structureShape) {
        final ShapeId shapeId = structureShape.getId();

        // The Dafny type of a reference structure is the Dafny trait for its referent
        final Optional<ReferenceTrait> referenceTrait = structureShape.getTrait(ReferenceTrait.class);
        if (referenceTrait.isPresent()) {
            return dafnyTypeForShape(referenceTrait.get().getReferentId());
        }

        // The Dafny type of a positional structure is the Dafny type of its sole member
        final Optional<ShapeId> positionalMember = ModelUtils.getPositionalStructureMember(structureShape);
        if (positionalMember.isPresent()) {
            return dafnyTypeForShape(positionalMember.get());
        }

        // The Dafny type of an error structure is the corresponding generated Dafny class
        if (structureShape.hasTrait(ErrorTrait.class)) {
            return "%s.%s".formatted(
                    DafnyNameResolver.dafnyExternNamespaceForShapeId(shapeId),
                    shapeId.getName(serviceShape));
        }

        // The Dafny type of other structures is simply the structure's name.
        // We explicitly specify the Dafny namespace just in case of collisions.
        return "%s._I%s".formatted(
                DafnyNameResolver.dafnyExternNamespaceForShapeId(shapeId),
                shapeId.getName(serviceShape));
    }

    /**
     * Returns the name of the concrete Dafny type for the given regular (i.e. not an enum or reference) structure.
     * <p>
     * This should only be used to access members absent from the abstract type, e.g. the constructor.
     */
    public String dafnyConcreteTypeForRegularStructure(final StructureShape structureShape) {
        final ShapeId shapeId = structureShape.getId();
        return "%s.%s".formatted(
                DafnyNameResolver.dafnyExternNamespaceForShapeId(shapeId),
                shapeId.getName(serviceShape));
    }

    private String dafnyTypeForMember(final MemberShape memberShape) {
        return memberShapeIsOptional(memberShape)
                ? dafnyTypeForOptionalMember(memberShape, false)
                : dafnyTypeForShape(memberShape.getTarget());

    }

    public String dafnyConcreteTypeForOptionalMember(final MemberShape memberShape) {
        return dafnyTypeForOptionalMember(memberShape, true);
    }

    private String dafnyTypeForOptionalMember(final MemberShape memberShape, final boolean concrete) {
        if (!memberShapeIsOptional(memberShape)) {
            throw new IllegalArgumentException("memberShape must be optional");
        }

        final String baseType = dafnyTypeForShape(memberShape.getTarget());
        final String prefix = concrete ? "" : "_I";
        return "Wrappers_Compile.%sOption<%s>".formatted(prefix, baseType);
    }

    private String dafnyTypeForService(final ServiceShape serviceShape) {
        final ShapeId serviceShapeId = serviceShape.getId();
        return "%s.%sClient".formatted(DafnyNameResolver.dafnyExternNamespaceForShapeId(serviceShapeId), interfaceForService(serviceShapeId));
    }

    private String dafnyTypeForResource(final ResourceShape resourceShape) {
        final ShapeId resourceShapeId = resourceShape.getId();
        return "%s.%s".formatted(DafnyNameResolver.dafnyExternNamespaceForShapeId(resourceShapeId), interfaceForResource(resourceShapeId));
    }

    /**
     * Returns the abstract Dafny type representing errors for the given service.
     * <p>
     * This should generally be preferred to using the concrete Dafny type;
     * see {@link DotNetNameResolver#dafnyConcreteTypeForServiceError(ServiceShape)}.
     * <p>
     * TODO remove this for error refactoring
     */
    public String dafnyAbstractTypeForServiceError(final ServiceShape serviceShape) {
        return "%s._I%sError".formatted(
                DafnyNameResolver.dafnyExternNamespaceForShapeId(serviceShape.getId()),
                serviceShape.getContextualName(serviceShape));
    }

    /**
     * Returns the concrete Dafny type representing errors for the given service.
     * <p>
     * This must be used for accessing particular error constructors;
     * otherwise, prefer to use the abstract Dafny type
     * ({@link DotNetNameResolver#dafnyAbstractTypeForServiceError(ServiceShape)}).
     * <p>
     * TODO remove this for error refactoring
     */
    public String dafnyConcreteTypeForServiceError(final ServiceShape serviceShape) {
        return "%s.%sError".formatted(
                DafnyNameResolver.dafnyExternNamespaceForShapeId(serviceShape.getId()),
                serviceShape.getContextualName(serviceShape));
    }

    /**
     * Returns the Dafny trait implemented by all errors in the given service.
     * <p>
     * This is distinct from the specific Dafny error classes, since the trait / common error shape is not modeled.
     * To get the type for a specific Dafny error class, pass the corresponding structure shape to
     * {@link DotNetNameResolver#dafnyTypeForShape(ShapeId)}.
     */
    public String dafnyTypeForCommonServiceError(final ServiceShape serviceShape) {
        if (serviceShape.getId().getName(serviceShape).equals("AwsEncryptionSdkFactory")) {
            return "%s.IAwsEncryptionSdkException".formatted(DafnyNameResolver.dafnyExternNamespaceForShapeId(serviceShape.getId()));
        } else if (serviceShape.getId().getName(serviceShape).equals("AwsCryptographicMaterialProvidersFactory")) {
            return "%s.IAwsCryptographicMaterialProvidersException".formatted(DafnyNameResolver.dafnyExternNamespaceForShapeId(serviceShape.getId()));
        }
        return "%s.I%sException".formatted(
                DafnyNameResolver.dafnyExternNamespaceForShapeId(serviceShape.getId()),
                serviceShape.getContextualName(serviceShape)
        );
    }

    /**
     * Returns the compiled-Dafny return type for an operation of this service.
     * This is the compiled-Dafny {@code Result<T, E>},
     * where {@code T} is the corresponding Dafny-compiled value type as determined below,
     * and where {@code E} is the Dafny-compiled common error type for this service.
     * <ul>
     *     <li>If the operation has output, the value type is the corresponding compiled-Dafny output type.</li>
     *     <li>If the operation has no output, the value type is the compiled-Dafny {@code ()} ("unit").</li>
     * </ul>
     */
    public String dafnyTypeForServiceOperationOutput(final OperationShape operationShape) {
        return dafnyTypeForServiceOperationOutput(operationShape, false);
    }

    /**
     * Like {@link DotNetNameResolver#dafnyTypeForServiceOperationOutput(OperationShape)}, but if the {@code concrete}
     * parameter is {@code true}, then the concrete compiled-Dafny {@code Result} is returned instead of the abstract
     * compiled-Dafny {@code Result} ("_IResult").
     * <p>
     * The difference is that the abstract {@code Result} is emitted by the Dafny compiler when specifying contracts
     * (such as method parameter and return types),
     * whereas the concrete {@code Result} must be used to invoke the {@code create_Success} and
     * {@code create_Failure} constructors.
     */
    public String dafnyTypeForServiceOperationOutput(final OperationShape operationShape, final boolean concrete) {
        final String outputType = operationShape.getOutput()
                .map(this::dafnyTypeForShape)
                .orElse(dafnyTypeForUnit());
        final String errorType = dafnyTypeForCommonServiceError(serviceShape);
        return dafnyTypeForResult(outputType, errorType, concrete);
    }

    ;

    private String dafnyTypeForResult(final String valueType, final String errorType, final boolean concrete) {
        final String resultType = concrete ? "Result" : "_IResult";
        return "Wrappers_Compile.%s<%s, %s>".formatted(resultType, valueType, errorType);
    }

    public String dafnyTypeForUnit() {
        return "_System._ITuple0";
    }

    public String dafnyValueForUnit() {
        return "_System.Tuple0.Default()";
    }

    /**
     * Returns the name of the compiled-Dafny implementation of the service client.
     * <p>
     * Note that the service client lives in a sub-namespace of the same name. This is because the generated Dafny API
     * skeleton uses the plain "Dafny.(service namespace)" namespace, and implementations cannot use the same extern
     * namespace.
     * <p>
     * FIXME: remove this workaround once Dafny allows duplicate extern namespaces
     */
    public String dafnyImplForServiceClient() {
        return "%1$s.%2$s.%2$s".formatted(DafnyNameResolver.dafnyExternNamespaceForShapeId(serviceShape.getId()), clientForService());
    }

    public String dafnyImplForFactory() {
        return "%1$s.%2$s.%2$s".formatted(DafnyNameResolver.dafnyExternNamespaceForShapeId(serviceShape.getId()), staticFactoryForService());
    }

    public boolean memberShapeIsOptional(final MemberShape memberShape) {
        return ModelUtils.memberShapeIsOptional(model, memberShape);
    }

    /**
     * Encodes a shape ID as a unique valid C# identifier.
     * <p>
     * The encoding of a shape ID consists of type-length-value encodings of each of its "parts", separated by two
     * underscores. For example, "foo.bar#Shape$Member" is encoded as <code>N3_foo__N3_bar__S5_Shape__M6_Member</code>.
     * <p>
     * The encoding scheme has some redundancy in order to aid legibility of encoded "normal" shape IDs, such as the
     * redundant double-underscore between "parts". But even an inscrutable encoding (arising from a pathological shape
     * ID) has a unique parse, so there is no concern for an encoding collision.
     * <p>
     * (Note: we never need to actually parse this identifier.)
     */
    @VisibleForTesting
    public static String encodedIdentForShapeId(final ShapeId shapeId) {
        final String namespace = shapeId.getNamespace();
        final String relativeShape = shapeId.getName();
        final Optional<String> memberOptional = shapeId.getMember();

        // "N" for namespace
        final List<String> encodedParts = new ArrayList<>();
        for (final String namespacePart : namespace.split("\\.")) {
            encodedParts.add(String.format("N%d_%s", namespacePart.length(), namespacePart));
        }
        // "S" for relative shape
        encodedParts.add(String.format("S%d_%s", relativeShape.length(), relativeShape));
        // "M" for member
        if (memberOptional.isPresent()) {
            final String member = memberOptional.get();
            encodedParts.add(String.format("M%d_%s", member.length(), member));
        }

        return Joiner.on("__").join(encodedParts);
    }

    public Model getModel() {
        return model;
    }

    public ServiceShape getServiceShape() {
        return serviceShape;
    }

    @Override
    public boolean equals(Object obj) {
        if (obj == this) return true;
        if (obj == null || obj.getClass() != this.getClass()) return false;
        var that = (DotNetNameResolver) obj;
        return Objects.equals(this.model, that.model) &&
                Objects.equals(this.serviceShape, that.serviceShape);
    }

    @Override
    public int hashCode() {
        return Objects.hash(model, serviceShape);
    }

    @Override
    public String toString() {
        return "CSharpNameResolver[" +
                "model=" + model + ", " +
                "serviceShape=" + serviceShape + ']';
    }
}
