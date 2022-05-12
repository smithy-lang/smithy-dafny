// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import com.google.common.annotations.VisibleForTesting;
import com.google.common.collect.Sets;

import software.amazon.polymorph.traits.ExtendableTrait;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.traits.ClientConfigTrait;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.polymorph.utils.Token;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.BlobShape;
import software.amazon.smithy.model.shapes.BooleanShape;
import software.amazon.smithy.model.shapes.IntegerShape;
import software.amazon.smithy.model.shapes.ListShape;
import software.amazon.smithy.model.shapes.LongShape;
import software.amazon.smithy.model.shapes.MapShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.TimestampShape;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;

import java.nio.file.Path;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Queue;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static software.amazon.polymorph.smithydotnet.DotNetNameResolver.TYPE_CONVERSION_CLASS_NAME;
import static software.amazon.polymorph.smithydotnet.DotNetNameResolver.typeConverterForShape;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.FROM_DAFNY;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.TO_DAFNY;

/**
 * Generates a {@code TypeConversion} class that includes all {@link TypeConverter}s needed for the operations in the
 * provided {@link Model}.
 */
public class TypeConversionCodegen {
    /**
     * A pair of type converter methods that converts between the compiled Dafny representation and the idiomatic C#
     * representation of a given {@link software.amazon.smithy.model.shapes.Shape} value.
     */
    public static record TypeConverter(ShapeId shapeId, TokenTree fromDafny, TokenTree toDafny) {}

    public static final Path TYPE_CONVERSION_CLASS_PATH = Path.of(TYPE_CONVERSION_CLASS_NAME + ".cs");

    protected final Model model;
    protected final ServiceShape serviceShape;
    protected final DotNetNameResolver nameResolver;

    public TypeConversionCodegen(final Model model, final ShapeId serviceShapeId) {
        this(model, serviceShapeId,
                new DotNetNameResolver(model, model.expectShape(serviceShapeId, ServiceShape.class)));
    }

    public TypeConversionCodegen(final Model model, final ShapeId serviceShapeId, final DotNetNameResolver nameResolver) {
        this.model = model;
        this.serviceShape = model.expectShape(serviceShapeId, ServiceShape.class);
        this.nameResolver = nameResolver;
    }

    public Map<Path, TokenTree> generate() {
        final TokenTree prelude = TokenTree.of(
                // needed for LINQ operators like Select
                "using System.Linq;",
                // TODO: fully qualify types to avoid needing this
                "using AWS.EncryptionSDK.Core;"
                );
        final Stream<TypeConverter> modeledConverters = findShapeIdsToConvert()
                .stream()
                .map(model::expectShape)
                .map(this::generateConverter);
        final Stream<TypeConverter> unmodeledConverters = Stream.of(generateCommonExceptionConverter());
        final Stream<TypeConverter> converters = Stream.concat(modeledConverters, unmodeledConverters);
        final TokenTree conversionClassBody = TokenTree.of(converters
                .flatMap(typeConverter -> Stream.of(typeConverter.fromDafny, typeConverter.toDafny)))
                .lineSeparated()
                .braced();
        final TokenTree conversionClass = conversionClassBody
                .prepend(TokenTree.of("internal static class", TYPE_CONVERSION_CLASS_NAME))
                .namespaced(Token.of(getTypeConversionNamespace()));
        return Map.of(TYPE_CONVERSION_CLASS_PATH, conversionClass.prepend(prelude));
    }

    /**
     * Returns all shape IDs that require converters.
     */
    @VisibleForTesting
    public Set<ShapeId> findShapeIdsToConvert() {
        final Set<ShapeId> shapesToConvert = new HashSet<>();

        // Breadth-first search via getDependencyShapeIds
        final Queue<ShapeId> toTraverse = new LinkedList<>(findInitialShapeIdsToConvert());
        while (!toTraverse.isEmpty()) {
            final ShapeId currentShapeId = toTraverse.remove();
            if (shapesToConvert.add(currentShapeId)) {
                final Shape currentShape = model.expectShape(currentShapeId);
                getDependencyShapeIds(currentShape).forEach(toTraverse::add);
            }
        }

        return shapesToConvert;
    }

    /**
     * Returns a set of shape IDs for which to start generating type converter pairs, by recursively traversing
     * services, resources, and operations defined in the model.
     * <p>
     * Since type converters are only necessary when calling API operations, it suffices to find the shape IDs of:
     * <ul>
     *     <li>operation input and output structures</li>
     *     <li>client configuration structures</li>
     *     <li>specific (modeled) error structures</li>
     * </ul>
     */
    private Set<ShapeId> findInitialShapeIdsToConvert() {
        // Collect services
        final Set<ServiceShape> serviceShapes = model.getServiceShapes().stream()
                .filter(serviceShape -> isInServiceNamespace(serviceShape.getId()))
                .collect(Collectors.toSet());

        // Collect resources defined in model...
        final Stream<ResourceShape> topLevelResourceShapes = model.getResourceShapes().stream()
                .filter(resourceShape -> isInServiceNamespace(resourceShape.getId()));
        // ... and resources of collected services.
        final Stream<ResourceShape> serviceResourceShapes = serviceShapes.stream()
                .flatMap(serviceShape -> serviceShape.getResources().stream())
                .map(resourceShapeId -> model.expectShape(resourceShapeId, ResourceShape.class));
        final Set<ResourceShape> resourceShapes = Stream.concat(topLevelResourceShapes, serviceResourceShapes)
                .collect(Collectors.toSet());

        // Collect operations defined in model...
        final Stream<OperationShape> topLevelOperationShapes = model.getOperationShapes().stream()
                .filter(operationShape -> isInServiceNamespace(operationShape.getId()));
        // ... and operations of collected services...
        final Stream<OperationShape> serviceOperationShapes = serviceShapes.stream()
                .flatMap(serviceShape -> serviceShape.getAllOperations().stream())
                .map(operationShapeId -> model.expectShape(operationShapeId, OperationShape.class));
        // ... and operations of collected resources.
        final Stream<OperationShape> resourceOperationShapes = resourceShapes.stream()
                .flatMap(resourceShape -> resourceShape.getAllOperations().stream())
                .map(operationShapeId -> model.expectShape(operationShapeId, OperationShape.class));
        final Set<OperationShape> operationShapes = Stream
                .of(topLevelOperationShapes, serviceOperationShapes, resourceOperationShapes)
                .flatMap(Function.identity())
                .collect(Collectors.toSet());

        // Collect inputs/output structures for collected operations
        final Set<ShapeId> operationStructures = operationShapes.stream()
                .flatMap(operationShape -> Stream
                        .of(operationShape.getInput(), operationShape.getOutput())
                        .flatMap(Optional::stream))
                .collect(Collectors.toSet());
        // Collect service client config structures
        final Set<ShapeId> clientConfigStructures = serviceShapes.stream()
                .map(serviceShape -> serviceShape.getTrait(ClientConfigTrait.class))
                .flatMap(Optional::stream)
                .map(ClientConfigTrait::getClientConfigId)
                .collect(Collectors.toSet());

        // Collect all specific error structures
        final Set<ShapeId> errorStructures = ModelUtils.streamServiceErrors(model, serviceShape)
                .map(Shape::getId)
                .collect(Collectors.toSet());

        return Stream.of(operationStructures, clientConfigStructures, errorStructures)
                .reduce(Sets::union).get();
    }

    private boolean isInServiceNamespace(final ShapeId shapeId) {
        return shapeId.getNamespace().equals(serviceShape.getId().getNamespace());
    }

    /**
     * Generates a {@link TypeConverter} for the given shape.
     */
    @SuppressWarnings("OptionalGetWithoutIsPresent")
    private TypeConverter generateConverter(final Shape shape) {
        return switch (shape.getType()) {
            case BLOB -> generateBlobConverter(shape.asBlobShape().get());
            case BOOLEAN -> generateBooleanConverter(shape.asBooleanShape().get());
            case STRING -> generateStringConverter(shape.asStringShape().get());
            case INTEGER -> generateIntegerConverter(shape.asIntegerShape().get());
            case LONG -> generateLongConverter(shape.asLongShape().get());
            case TIMESTAMP -> generateTimestampConverter(shape.asTimestampShape().get());
            case LIST -> generateListConverter(shape.asListShape().get());
            case MAP -> generateMapConverter(shape.asMapShape().get());
            case STRUCTURE -> generateStructureConverter(shape.asStructureShape().get());
            case MEMBER -> generateMemberConverter(shape.asMemberShape().get());
            default -> throw new IllegalStateException();
        };
    }

    /**
     * Returns dependency shape IDs for the given shape. A shape {@code S} has a dependency shape {@code D} if a type
     * converter for {@code S} requires the existence of a type converter for {@code D}.
     */
    @SuppressWarnings("OptionalGetWithoutIsPresent")
    private Stream<ShapeId> getDependencyShapeIds(final Shape shape) {
        return switch (shape.getType()) {
            case LIST -> Stream.of(shape.asListShape().get().getMember().getId());
            case MAP -> {
                final MapShape mapShape = shape.asMapShape().get();
                yield Stream.of(mapShape.getKey().getId(), mapShape.getValue().getId());
            }
            case STRUCTURE -> ModelUtils.streamStructureMembers(shape.asStructureShape().get()).map(Shape::getId);
            case MEMBER -> Stream.of(shape.asMemberShape().get().getTarget());
            default -> Stream.empty();
        };
    }

    public TypeConverter generateBlobConverter(final BlobShape blobShape) {
        final TokenTree fromDafnyBody = Token.of("return new System.IO.MemoryStream(value.Elements);");
        final TokenTree toDafnyBody = Token.of("return Dafny.Sequence<byte>.FromArray(value.ToArray());");
        return buildConverterFromMethodBodies(blobShape, fromDafnyBody, toDafnyBody);
    }

    public TypeConverter generateBooleanConverter(final BooleanShape booleanShape) {
        final TokenTree fromDafnyBody = Token.of("return value;");
        final TokenTree toDafnyBody = Token.of("return value;");
        return buildConverterFromMethodBodies(booleanShape, fromDafnyBody, toDafnyBody);
    }

    public TypeConverter generateStringConverter(final StringShape stringShape) {
        if (stringShape.hasTrait(EnumTrait.class)) {
            return generateEnumConverter(stringShape, stringShape.expectTrait(EnumTrait.class));
        }

        if (stringShape.hasTrait(DafnyUtf8BytesTrait.class)) {
            return generateUtf8BytesConverter(stringShape);
        }

        final TokenTree fromDafnyBody = Token.of("return new string(value.Elements);");
        final TokenTree toDafnyBody = Token.of("return Dafny.Sequence<char>.FromString(value);");
        return buildConverterFromMethodBodies(stringShape, fromDafnyBody, toDafnyBody);
    }

    public TypeConverter generateIntegerConverter(final IntegerShape integerShape) {
        final TokenTree fromDafnyBody = Token.of("return value;");
        final TokenTree toDafnyBody = Token.of("return value;");
        return buildConverterFromMethodBodies(integerShape, fromDafnyBody, toDafnyBody);
    }

    public TypeConverter generateLongConverter(final LongShape longShape) {
        final TokenTree fromDafnyBody = Token.of("return value;");
        final TokenTree toDafnyBody = Token.of("return value;");
        return buildConverterFromMethodBodies(longShape, fromDafnyBody, toDafnyBody);
    }

    public TypeConverter generateTimestampConverter(final TimestampShape timestampShape) {
        final TokenTree fromDafnyBody = Token.of("""
                System.Globalization.CultureInfo culture = new System.Globalization.CultureInfo("");
                string timestampString = new string(value.Elements);
                return System.DateTime.ParseExact(timestampString, "s", culture);
                """);
        final TokenTree toDafnyBody = Token.of("""
                System.Globalization.CultureInfo culture = new System.Globalization.CultureInfo("");
                string timestampString = value.ToString("s", culture);
                return Dafny.Sequence<char>.FromString(timestampString);
                """);
        return buildConverterFromMethodBodies(timestampShape, fromDafnyBody, toDafnyBody);
    }

    protected boolean enumListMembersAreStringsInCSharp() {
        return false;
    }

    public TypeConverter generateListConverter(final ListShape listShape) {
        final String listCSharpType = nameResolver.baseTypeForList(listShape);

        final MemberShape memberShape = listShape.getMember();
        final String memberDafnyType = nameResolver.dafnyTypeForShape(memberShape.getId());
        final String memberCSharpType = nameResolver.baseTypeForMember(memberShape);;

        final String memberToDafnyConverterName = typeConverterForShape(memberShape.getId(), TO_DAFNY);
        final String memberFromDafnyConverterName = typeConverterForShape(memberShape.getId(), FROM_DAFNY);

        final boolean convertMemberEnumToString = enumListMembersAreStringsInCSharp()
            && model.expectShape(memberShape.getTarget()).hasTrait(EnumTrait.class);
        final String fromDafnyEnumConversion = convertMemberEnumToString
                ? ".Select<%s, string>(x => x)".formatted(memberCSharpType)
                : "";
        final String toDafnyEnumConversion = convertMemberEnumToString
                ? ".Select<string, %s>(x => x)".formatted(memberCSharpType)
                : "";

        final TokenTree fromDafnyBody = Token.of(
                "return new %s(value.Elements.Select(%s)%s);".formatted(
                        listCSharpType,
                        memberFromDafnyConverterName,
                        fromDafnyEnumConversion));

        final TokenTree toDafnyBody = Token.of(
                "return Dafny.Sequence<%s>.FromArray(value%s.Select(%s).ToArray());".formatted(
                        memberDafnyType,
                        toDafnyEnumConversion,
                        memberToDafnyConverterName));

        return buildConverterFromMethodBodies(listShape, fromDafnyBody, toDafnyBody);
    }

    public TypeConverter generateMapConverter(final MapShape mapShape) {
        final MemberShape keyShape = mapShape.getKey();
        final MemberShape valueShape = mapShape.getValue();
        final String keyDafnyType = nameResolver.dafnyTypeForShape(keyShape.getId());
        final String valueDafnyType = nameResolver.dafnyTypeForShape(valueShape.getId());

        final String keyToDafnyConverterName = typeConverterForShape(keyShape.getId(), TO_DAFNY);
        final String keyFromDafnyConverterName = typeConverterForShape(keyShape.getId(), FROM_DAFNY);
        final String valueToDafnyConverterName = typeConverterForShape(valueShape.getId(), TO_DAFNY);
        final String valueFromDafnyConverterName = typeConverterForShape(valueShape.getId(), FROM_DAFNY);

        final TokenTree fromDafnyBody = Token.of(
                "return value.ItemEnumerable.ToDictionary(pair => %s(pair.Car), pair => %s(pair.Cdr));"
                        .formatted(keyFromDafnyConverterName, valueFromDafnyConverterName));

        final String dafnyMapTypeArgs = "<%s, %s>".formatted(keyDafnyType, valueDafnyType);
        final TokenTree toDafnyBody = Token.of("""
                return Dafny.Map%s.FromCollection(value.Select(pair =>
                    new Dafny.Pair%s(%s(pair.Key), %s(pair.Value))
                ));"""
                .formatted(dafnyMapTypeArgs, dafnyMapTypeArgs, keyToDafnyConverterName, valueToDafnyConverterName));
        return buildConverterFromMethodBodies(mapShape, fromDafnyBody, toDafnyBody);
    }

    public TypeConverter generateStructureConverter(final StructureShape structureShape) {
        final Optional<ReferenceTrait> referenceTraitOptional = structureShape.getTrait(ReferenceTrait.class);
        if (referenceTraitOptional.isPresent()) {
            return generateReferenceStructureConverter(structureShape, referenceTraitOptional.get());
        }

        final Optional<PositionalTrait> positionalTraitOptional = structureShape.getTrait(PositionalTrait.class);
        if (positionalTraitOptional.isPresent()) {
            return generatePositionalStructureConverter(structureShape);
        }

        if (structureShape.hasTrait(ErrorTrait.class)) {
            return generateSpecificExceptionConverter(structureShape);
        }

        return generateRegularStructureConverter(structureShape);
    }

    /**
     * This should not be called directly, instead call
     * {@link TypeConversionCodegen#generateStructureConverter(StructureShape)}.
     */
    private TypeConverter generateRegularStructureConverter(final StructureShape structureShape) {
        final TokenTree concreteVar = Token.of("%1$s concrete = (%1$s)value;".formatted(
                nameResolver.dafnyConcreteTypeForRegularStructure(structureShape)));
        final TokenTree assignments = TokenTree.of(ModelUtils.streamStructureMembers(structureShape)
                .map(memberShape -> {
                    final String dafnyMemberName = memberShape.getMemberName();
                    final String propertyName = nameResolver.classPropertyForStructureMember(memberShape);
                    final String propertyType = nameResolver.classPropertyTypeForStructureMember(memberShape);
                    final String memberFromDafnyConverterName = typeConverterForShape(
                            memberShape.getId(), FROM_DAFNY);

                    final TokenTree checkIfPresent;
                    if (nameResolver.memberShapeIsOptional(memberShape)) {
                        checkIfPresent = Token.of("if (concrete.%s.is_Some)".formatted(dafnyMemberName));
                    } else {
                        checkIfPresent = TokenTree.empty();
                    }
                    final TokenTree assign = Token.of("converted.%s = (%s) %s(concrete.%s);".formatted(
                            propertyName, propertyType, memberFromDafnyConverterName, dafnyMemberName));
                    return TokenTree.of(checkIfPresent, assign);
                })).lineSeparated();
        final String structureType = nameResolver.baseTypeForShape(structureShape.getId());
        final TokenTree fromDafnyBody = TokenTree.of(
                concreteVar,
                Token.of("%1$s converted = new %1$s();".formatted(structureType)),
                assignments,
                Token.of("return converted;")
        );

        final TokenTree isSetTernaries = TokenTree.of(
                ModelUtils.streamStructureMembers(structureShape)
                        .filter(nameResolver::memberShapeIsOptional)
                        .map(this::generateExtractOptionalMember)
        ).lineSeparated();

        final TokenTree constructorArgs = TokenTree.of(ModelUtils.streamStructureMembers(structureShape)
                .map(this::generateConstructorArg)
                .map(Token::of)
        ).separated(Token.of(','));
        final TokenTree constructor = TokenTree.of(
                TokenTree.of("return new"),
                TokenTree.of(nameResolver.dafnyConcreteTypeForRegularStructure(structureShape)),
                constructorArgs.parenthesized(),
                Token.of(';')
        );
        final TokenTree toDafnyBody = TokenTree.of(
                isSetTernaries,
                constructor
        ).lineSeparated();

        return buildConverterFromMethodBodies(structureShape, fromDafnyBody, toDafnyBody);
    }

    /**
     * Returns either:
     * "ToDafny_memberShape(value.PropertyName)"
     * OR :
     * "ToDafny_memberShape(propertyName)"
     */
    private String generateConstructorArg(final MemberShape memberShape) {
        if (nameResolver.memberShapeIsOptional(memberShape)) {
            return "%s(%s)".formatted(
                    typeConverterForShape(memberShape.getId(), TO_DAFNY),
                    nameResolver.variableNameForClassProperty(memberShape));
        }
        return "%s(value.%s)".formatted(
                typeConverterForShape(memberShape.getId(), TO_DAFNY),
                nameResolver.classPropertyForStructureMember(memberShape));
    }

    /**
     * Returns:
     * "type varName = value.IsSetPropertyName() ? value.PropertyName : (type) null;"
     */
    public TokenTree generateExtractOptionalMember(final MemberShape memberShape) {
        final String type = nameResolver.baseTypeForShape(memberShape.getId());
        final String varName = nameResolver.variableNameForClassProperty(memberShape);
        final String isSetMethod = nameResolver.isSetMethodForStructureMember(memberShape);
        final String propertyName = nameResolver.classPropertyForStructureMember(memberShape);
        return TokenTree.of(
                type,
                varName,
                "= value.%s()".formatted(isSetMethod),
                "? value.%s :".formatted(propertyName),
                "(%s) null;".formatted(type)
        );
    }

    public TypeConverter generateMemberConverter(final MemberShape memberShape) {
        final Shape targetShape = model.expectShape(memberShape.getTarget());

        final String targetFromDafnyConverterName = typeConverterForShape(targetShape.getId(), FROM_DAFNY);
        final String targetToDafnyConverterName = typeConverterForShape(targetShape.getId(), TO_DAFNY);

        if (!nameResolver.memberShapeIsOptional(memberShape)) {
            final TokenTree fromDafnyBody = Token.of("return %s(value);".formatted(targetFromDafnyConverterName));
            final TokenTree toDafnyBody = Token.of("return %s(value);".formatted(targetToDafnyConverterName));
            return buildConverterFromMethodBodies(memberShape, fromDafnyBody, toDafnyBody);
        }

        final String cSharpType = nameResolver.baseTypeForShape(targetShape.getId());
        final String cSharpOptionType = nameResolver.baseTypeForShape(memberShape.getId());
        final String dafnyOptionType = nameResolver.dafnyConcreteTypeForOptionalMember(memberShape);
        final TokenTree fromDafnyBody = Token.of("return value.is_None ? (%s) null : %s(value.Extract());"
                .formatted(cSharpOptionType, targetFromDafnyConverterName));
        final TokenTree toDafnyBody = Token.of(
                "return value == null ? %s.create_None() : %s.create_Some(%s((%s) value));"
                .formatted(dafnyOptionType, dafnyOptionType, targetToDafnyConverterName, cSharpType));
        return buildConverterFromMethodBodies(memberShape, fromDafnyBody, toDafnyBody);
    }

    /**
     * This should not be called directly, instead call
     * {@link TypeConversionCodegen#generateStructureConverter(StructureShape)}.
     */
    protected TypeConverter generateReferenceStructureConverter(
            final StructureShape structureShape, final ReferenceTrait referenceTrait) {
        final ShapeId referentId = referenceTrait.getReferentId();
        return switch (referenceTrait.getReferentType()) {
            case SERVICE -> generateServiceReferenceStructureConverter(
                    structureShape, model.expectShape(referentId, ServiceShape.class));
            case RESOURCE -> generateResourceReferenceStructureConverter(
                    structureShape, model.expectShape(referentId, ResourceShape.class));
        };
    }

    /**
     * This should not be called directly, instead call
     * {@link TypeConversionCodegen#generateStructureConverter(StructureShape)}.
     *
     * Note that this currently only allows for C# implementations of AWS SDK service interfaces.
     */
    protected TypeConverter generateServiceReferenceStructureConverter(
            final StructureShape structureShape, final ServiceShape serviceShape) {
        // TODO is this actually a good filter for AWS SDK services?
        if (!serviceShape.getId().getNamespace().startsWith("com.amazonaws.")) {
            throw new UnsupportedOperationException("Only AWS SDK service client converters are supported");
        }

        final AwsSdkTypeConversionCodegen awsSdkTypeConversionCodegen =
                new AwsSdkTypeConversionCodegen(model, serviceShape.getId());
        return awsSdkTypeConversionCodegen.generateAwsSdkServiceReferenceStructureConverter(structureShape);
    }

    /**
     * This should not be called directly, instead call
     * {@link TypeConversionCodegen#generateStructureConverter(StructureShape)}.
     */
    protected TypeConverter generateResourceReferenceStructureConverter(
            final StructureShape structureShape, final ResourceShape resourceShape) {
        final ShapeId resourceShapeId = resourceShape.getId();
        final String shimClass = nameResolver.shimClassForResource(resourceShapeId);
        final String baseType = nameResolver.baseTypeForShape(resourceShapeId);
        if (!resourceShape.hasTrait(ExtendableTrait.class)) {
            final TokenTree fromDafnyBody = Token.of("return new %s(value);"
                    .formatted(nameResolver.shimClassForResource(resourceShapeId)));
            final TokenTree toDafnyBody = Token.of("""
                    if (value is %s valueWithImpl) {
                        return valueWithImpl._impl;
                    }
                    throw new System.ArgumentException("Custom implementations of %s are not supported");
                    """.formatted(shimClass, baseType));
            return buildConverterFromMethodBodies(structureShape, fromDafnyBody, toDafnyBody);
        }
        final String nativeWrapperClass = nameResolver.nativeWrapperClassForResource(resourceShapeId);
        final String baseClass = nameResolver.baseClassForResource(resourceShapeId);
        final TokenTree fromDafnyBody = Token.of("""
                if (value is %s nativeWrapper) return nativeWrapper._impl;
                return new %s(value);
                """
                .formatted(nativeWrapperClass, shimClass)
        );
        TokenTree cases = TokenTree.of("""
                case %s valueWithImpl:
                    return valueWithImpl._impl;
                """.formatted(shimClass));
        cases = cases.append(TokenTree.of("""
                case %s nativeImpl:
                    return new %s(nativeImpl);
                """.formatted(baseClass, nativeWrapperClass)));
        cases = cases.append(TokenTree.of("""
                default:
                    throw new System.ArgumentException(
                        "Custom implementations of %s must extend %s.");"""
                .formatted(shimClass, baseClass)));
        final TokenTree toDafnyBody = Token.of("switch (value)")
                .append(cases.braced()).lineSeparated();
        return buildConverterFromMethodBodies(structureShape, fromDafnyBody, toDafnyBody);
    }

    /**
     * This should not be called directly, instead call
     * {@link TypeConversionCodegen#generateStructureConverter(StructureShape)}.
     */
    private TypeConverter generatePositionalStructureConverter(final StructureShape structureShape) {
        final ShapeId memberShapeId = ModelUtils.getPositionalStructureMember(structureShape).orElseThrow();

        final String memberFromDafnyConverterName = typeConverterForShape(memberShapeId, FROM_DAFNY);
        final String memberToDafnyConverterName = typeConverterForShape(memberShapeId, TO_DAFNY);
        final TokenTree fromDafnyBody = Token.of("return %s(value);".formatted(memberFromDafnyConverterName));
        final TokenTree toDafnyBody = Token.of("return %s(value);".formatted(memberToDafnyConverterName));

        return buildConverterFromMethodBodies(structureShape, fromDafnyBody, toDafnyBody);
    }

    /**
     * A pair of names for a {@link software.amazon.smithy.model.traits.EnumDefinition}, consisting of the
     * Smithy-defined name (the {@link EnumDefNames#defName}) and the Dafny-compiler-generated name (the
     * {@link EnumDefNames#dafnyName}).
     */
    private static record EnumDefNames(String defName, String dafnyName) {}

    /**
     * This should not be called directly, instead call
     * {@link TypeConversionCodegen#generateStringConverter(StringShape)}.
     */
    private TypeConverter generateEnumConverter(final StringShape stringShape, final EnumTrait enumTrait) {
        assert enumTrait.hasNames();
        //noinspection OptionalGetWithoutIsPresent
        final List<EnumDefNames> defNames = enumTrait.getValues().stream()
                .map(enumDefinition -> enumDefinition.getName().get())
                .map(name -> new EnumDefNames(name, DotNetNameResolver.dafnyCompiledNameForEnumDefinitionName(name)))
                .toList();
        final String enumClass = nameResolver.baseTypeForShape(stringShape.getId());
        final String dafnyEnumConcreteType = nameResolver.dafnyConcreteTypeForEnum(stringShape.getId());
        final Token throwInvalidEnumValue = Token.of("\nthrow new System.ArgumentException(\"Invalid %s value\");"
                .formatted(enumClass));

        final TokenTree fromDafnyBody = TokenTree.of(defNames.stream()
                .map(names -> "if (value.is_%s) return %s.%s;".formatted(names.dafnyName, enumClass, names.defName))
                .map(Token::of))
                .lineSeparated()
                .append(throwInvalidEnumValue);

        final TokenTree toDafnyBody = TokenTree.of(defNames.stream()
                .map(names -> {
                    final String condition = "%s.%s.Equals(value)".formatted(enumClass, names.defName);
                    // Dafny generates just "create" instead of "create_FOOBAR" if there's only one ctor
                    final String createSuffix = defNames.size() == 1
                        ? ""
                        : "_%s".formatted(names.dafnyName);
                    return "if (%s) return %s.create%s();".formatted(condition, dafnyEnumConcreteType, createSuffix);
                })
                .map(Token::of))
                .lineSeparated()
                .append(throwInvalidEnumValue);

        return buildConverterFromMethodBodies(stringShape, fromDafnyBody, toDafnyBody);
    }

    /**
     * @see DafnyUtf8BytesTrait
     */
    private TypeConverter generateUtf8BytesConverter(final StringShape stringShape) {
        final TokenTree fromDafnyBody = Token.of("""
                System.Text.UTF8Encoding utf8 = new System.Text.UTF8Encoding(false, true);
                return utf8.GetString(value.Elements);""");
        final TokenTree toDafnyBody = Token.of("""
                System.Text.UTF8Encoding utf8 = new System.Text.UTF8Encoding(false, true);
                return Dafny.Sequence<byte>.FromArray(utf8.GetBytes(value));""");
        return buildConverterFromMethodBodies(stringShape, fromDafnyBody, toDafnyBody);
    }

    /**
     * Generates Converters From/To Dafny/dotnet for Exceptions.
     * <p>
     *     In Polymorph, all of a Service's Exceptions descend from a root Service Exception.<br>
     *     On the C# side, this is represented by <code>ServiceBaseException</code>,
     *     which extends from <code>System.Exception</code>.<br>
     *     On the Dafny side, this is represented by <code>IServiceException</code>,
     *     which is a <code>trait</code>.<br>
     *
     *     Specific Exceptions, which come from the Smithy Model, extend these Exception roots
     *     and are modeled in both C# and Dafny explicitly.
     *     Polymorph generates converters for these specific, concrete, exceptions;
     *     these converters are utilized by this general converter.<br>
     *
     *     There are two special cases:<br>
     *
     *     1. Exceptions that extend the root exception but that are not in the Smithy Model.<br>
     *
     *     2. C# Exceptions that extend <code>System.Exception</code>.<br>
     *
     *     An Example of (1): a Customer implemented Keyring returns a Customer created Exception that extends form the root.<br>
     *
     *     An Example of (2): During execution, a C# interrupt exception is thrown.<br>
     *
     *     To protect the soundness of our GeneratedFromDafny code,
     *     we need to convert these special cases into objects that Dafny expects.
     *     Dafny does not have a native concept of Exceptions.
     *     So we must convert these into the only Dafny exception available to us: The root service exception.
     *
     *     This allows our Dafny code to wrap these exceptions into the <code>_IResult&lt;Success_type,Failure_type></code>
     *     it expects to handle, preserving Dafny's soundness.
     *
     *     As such, the generated methods are named distinctively:<br>
     *     - TO_DAFNY is named <code>ToDafny_CommonError</code>,
     *     as it will except any <code>System.Exception</code>.<br>
     *
     *     - FROM_DAFNY is named <code>FromDafny_CommonError_ServiceBaseException</code>,
     *     as it will only yield descends of <code>ServiceBaseException</code> or <code>ServiceBaseException</code> itself.<br>
     * </p>
     */
    public TypeConverter generateCommonExceptionConverter() {
        // Gather the Smithy Modeled specific exceptions by collecting them into a TreeSet.
        // This sorts the set by shape ID, making the order deterministic w.r.t the model.
        final TreeSet<StructureShape> errorShapes = ModelUtils.streamServiceErrors(model, serviceShape)
                .collect(Collectors.toCollection(TreeSet::new));
        final String cSharpType = "%s.%s".formatted(nameResolver.namespaceForService(), nameResolver.classForBaseServiceException());
        final String dafnyType = nameResolver.dafnyTypeForCommonServiceError(serviceShape);

        // Generate the FROM_DAFNY method
        // Handle the modeled exceptions.
        final TokenTree modeledExceptionsFromDafny = TokenTree.of(errorShapes.stream().map(errorShape -> {
            final ShapeId modeledErrorShapeId = errorShape.getId();
            return Token.of("case %1$s dafnyVal:\nreturn %2$s(dafnyVal);".formatted(
                    nameResolver.dafnyTypeForShape(modeledErrorShapeId),
                    typeConverterForShape(modeledErrorShapeId, FROM_DAFNY)
            ));
        })).lineSeparated();

        // Handle the special cases that were cast to the root service exception.
        final TokenTree handleBaseFromDafny = Token.of(
                "default:\nreturn new %s(\n%s(value.GetMessage()));".formatted(
                        cSharpType, typeConverterForShape(ShapeId.from("smithy.api#String"), FROM_DAFNY))
        );

        // Wrap all the converters into a switch statement.
        final TokenTree fromDafnySwitchCases = TokenTree.of(modeledExceptionsFromDafny, handleBaseFromDafny)
                .lineSeparated().braced();
        final TokenTree fromDafnyBody = TokenTree.of(
                TokenTree.of("switch(value)"), fromDafnySwitchCases).lineSeparated();
        final TokenTree fromDafnyConverterSignature = Token.of("public static %s %s(%s value)".formatted(
                cSharpType, nameResolver.typeConverterForCommonError(serviceShape, FROM_DAFNY), dafnyType));
        final TokenTree fromDafnyConverterMethod = TokenTree.of(fromDafnyConverterSignature, fromDafnyBody.braced());

        // Generate the TO_DAFNY method
        // Handle the modeled exceptions.
        final TokenTree specificExceptionsToDafny = TokenTree.of(errorShapes.stream().map(errorShape -> {
            final ShapeId specificErrorShapeId = errorShape.getId();
            return Token.of("case %1$s exception:\n return %2$s(exception);".formatted(
                    nameResolver.baseTypeForShape(specificErrorShapeId),
                    typeConverterForShape(specificErrorShapeId, TO_DAFNY)
            ));
        })).lineSeparated();
        // Handle the first special case; extensions of the service root exception that are not in the smithy model.
        final TokenTree handleBaseToDafny = Token.of(
                "case %1$s exception:\nrtn = new %2$s();\nrtn.message = %3$s(exception.Message);\nreturn rtn;"
                .formatted(cSharpType, nameResolver.dafnyBaseTypeForServiceError(),
                        typeConverterForShape(ShapeId.from("smithy.api#String"), TO_DAFNY)));
        // Handle the second special case; extensions of System.Exception.
        // Construct a custom message that details the Exception's type and message.
        final String anyMessage =
                """
                var message = $"%s encountered unexpected: {value.GetType()}: \\"{value.Message}\\"";"""
                        .formatted(nameResolver.serviceNameWithoutFactory());
        // Return the root service exception with the custom message.
        final TokenTree handleAnyException = Token.of(
                "default:\n%1$s\nrtn = new %2$s();\nrtn.message = %3$s(message);\nreturn rtn;"
                        .formatted(anyMessage, nameResolver.dafnyBaseTypeForServiceError(),
                                typeConverterForShape(ShapeId.from("smithy.api#String"), TO_DAFNY)));

        // Wrap all the converters into a switch statement.
        final TokenTree toDafnySwitchCases = TokenTree.of(specificExceptionsToDafny, handleBaseToDafny, handleAnyException)
                .lineSeparated().braced();
        final TokenTree toDafnyBody = TokenTree.of(
                TokenTree.of("%s rtn;\nswitch (value)\n".formatted(nameResolver.dafnyBaseTypeForServiceError())),
                toDafnySwitchCases);
        final TokenTree toDafnyConverterSignature = Token.of("public static %s %s(System.Exception value)".formatted(
                dafnyType, nameResolver.typeConverterForCommonError(serviceShape, TO_DAFNY)));
        final TokenTree toDafnyConverterMethod = TokenTree.of(toDafnyConverterSignature, toDafnyBody.braced());

        // The Common Exception Converter is novel to Polymorph, it is not native to smithy.
        // As such, it needs a shape ID. That shape ID must not conflict with anything else.
        final ShapeId syntheticShapeId = ShapeId.fromParts(serviceShape.getId().getNamespace(), "__SYNTHETIC_COMMON_ERROR");
        return new TypeConverter(syntheticShapeId, fromDafnyConverterMethod, toDafnyConverterMethod);
    }

    /**
     * Returns a type converter for an {@code @error} structure.
     * <p>
     * This requires special-casing because a System.Exception's {@code message} field cannot be set by property, but
     * instead must be passed to the constructor.
     */
    public TypeConverter generateSpecificExceptionConverter(final StructureShape errorShape) {
        assert errorShape.hasTrait(ErrorTrait.class);
        assert errorShape.getMember("message").isPresent();
        final ShapeId messageShapeId = errorShape.getId().withMember("message");

        final Token fromDafnyBody = Token.of("return new %s(%s(value.message));".formatted(
                nameResolver.baseTypeForShape(errorShape.getId()),
                typeConverterForShape(messageShapeId, FROM_DAFNY)
        ));
        final Token toDafnyBody = Token.of("""
                %1$s converted = new %1$s();
                converted.message = %2$s(value.Message);
                return converted;
                """.formatted(
                        nameResolver.dafnyTypeForShape(errorShape.getId()),
                        typeConverterForShape(messageShapeId, TO_DAFNY)
        ));

        return buildConverterFromMethodBodies(errorShape, fromDafnyBody, toDafnyBody);
    }

    /**
     * Build a {@link TypeConverter} by surrounding the given type converter method bodies with appropriate method
     * signatures. Each method body should assume the sole argument (the value to convert) is named {@code value}.
     */
    protected TypeConverter buildConverterFromMethodBodies(
            final Shape shape, final TokenTree fromDafnyBody, final TokenTree toDafnyBody) {
        final String dafnyType = nameResolver.dafnyTypeForShape(shape.getId());
        final String cSharpType = nameResolver.baseTypeForShape(shape.getId());

        final String fromDafnyConverterName = typeConverterForShape(shape.getId(), FROM_DAFNY);
        final TokenTree fromDafnyConverterSignature = TokenTree.of(
                "public static", cSharpType, fromDafnyConverterName, "(%s value)".formatted(dafnyType));
        final TokenTree fromDafnyConverterMethod = TokenTree.of(fromDafnyConverterSignature, fromDafnyBody.braced());

        final String toDafnyConverterName = typeConverterForShape(shape.getId(), TO_DAFNY);
        final TokenTree toDafnyConverterSignature = TokenTree.of(
                "public static", dafnyType, toDafnyConverterName, "(%s value)".formatted(cSharpType));
        final TokenTree toDafnyConverterMethod = TokenTree.of(toDafnyConverterSignature, toDafnyBody.braced());

        return new TypeConverter(shape.getId(), fromDafnyConverterMethod, toDafnyConverterMethod);
    }

    /**
     * Returns the namespace in which to generate the type conversion class.
     *
     * Subclasses can override this in case it differs from the service's "main" namespace, e.g. in the case of AWS SDK
     * type conversion.
     */
    protected String getTypeConversionNamespace() {
        return nameResolver.namespaceForService();
    }

    @VisibleForTesting
    public Model getModel() {
        return model;
    }
}
