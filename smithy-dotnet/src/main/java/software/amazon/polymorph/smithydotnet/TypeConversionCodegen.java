// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import com.google.common.annotations.VisibleForTesting;
import com.google.common.collect.Sets;
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
                "using Aws.Crypto;"
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
                .namespaced(Token.of(nameResolver.namespaceForService()));
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

        final String memberToDafnyConverterName = DotNetNameResolver.typeConverterForShape(memberShape.getId(), TO_DAFNY);
        final String memberFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(memberShape.getId(), FROM_DAFNY);

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

        final String keyToDafnyConverterName = DotNetNameResolver.typeConverterForShape(keyShape.getId(), TO_DAFNY);
        final String keyFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(keyShape.getId(), FROM_DAFNY);
        final String valueToDafnyConverterName = DotNetNameResolver.typeConverterForShape(valueShape.getId(), TO_DAFNY);
        final String valueFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(valueShape.getId(), FROM_DAFNY);

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
                    final String memberFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(
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
                        .map(this::generateIsSetTernary)
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
    public String generateConstructorArg(final MemberShape memberShape) {
        if (nameResolver.memberShapeIsOptional(memberShape)) {
            return "%s(%s)".formatted(
                    DotNetNameResolver.typeConverterForShape(memberShape.getId(), TO_DAFNY),
                    nameResolver.variableNameForClassProperty(memberShape));
        }
        return "%s(value.%s)".formatted(
                DotNetNameResolver.typeConverterForShape(memberShape.getId(), TO_DAFNY),
                nameResolver.classPropertyForStructureMember(memberShape));
    }

    /**
     * Returns:
     * "type varName = value.IsSetPropertyName() ? value.PropertyName : (type) null;"
     */
    public TokenTree generateIsSetTernary(final MemberShape memberShape) {
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

        final String targetFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(targetShape.getId(), FROM_DAFNY);
        final String targetToDafnyConverterName = DotNetNameResolver.typeConverterForShape(targetShape.getId(), TO_DAFNY);

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
     *
     * Note that this currently only allows for Dafny-compiled implementations of the resource interface.
     *
     * TODO: allow for native C# implementations (i.e. customer-implemented) of resources
     */
    protected TypeConverter generateResourceReferenceStructureConverter(
            final StructureShape structureShape, final ResourceShape resourceShape) {
        final ShapeId resourceShapeId = resourceShape.getId();

        final TokenTree fromDafnyBody = Token.of("return new %s(value);"
                .formatted(nameResolver.shimClassForResource(resourceShapeId)));
        final TokenTree toDafnyBody = Token.of("""
                if (value is %s valueWithImpl) {
                    return valueWithImpl._impl;
                }
                throw new System.ArgumentException(\"Custom implementations of %s are not supported yet\");
                """.formatted(
                nameResolver.shimClassForResource(resourceShapeId),
                nameResolver.baseTypeForShape(resourceShapeId)));

        return buildConverterFromMethodBodies(structureShape, fromDafnyBody, toDafnyBody);
    }

    /**
     * This should not be called directly, instead call
     * {@link TypeConversionCodegen#generateStructureConverter(StructureShape)}.
     */
    private TypeConverter generatePositionalStructureConverter(final StructureShape structureShape) {
        final ShapeId memberShapeId = ModelUtils.getPositionalStructureMember(structureShape).orElseThrow();

        final String memberFromDafnyConverterName = DotNetNameResolver.typeConverterForShape(memberShapeId, FROM_DAFNY);
        final String memberToDafnyConverterName = DotNetNameResolver.typeConverterForShape(memberShapeId, TO_DAFNY);
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

    public TypeConverter generateCommonExceptionConverter() {
        // Collecting into a TreeSet sorts the set by shape ID, making the order deterministic w.r.t the model
        final TreeSet<StructureShape> errorShapes = ModelUtils.streamServiceErrors(model, serviceShape)
                .collect(Collectors.toCollection(TreeSet::new));
        final String commonExceptionName = nameResolver.classForCommonStaticFactoryException();
        final String cSharpType = "%s.%s".formatted(nameResolver.namespaceForService(), nameResolver.classForCommonStaticFactoryException());
        final String dafnyType = nameResolver.dafnyTypeForCommonServiceError(serviceShape);

        final TokenTree knownErrorsFromDafny = TokenTree.of(errorShapes.stream().map(errorShape -> {
            final ShapeId specificErrorShapeId = errorShape.getId();
            return Token.of("if (value is %1$s) return %2$s((%1$s) value);".formatted(
                    nameResolver.dafnyTypeForShape(specificErrorShapeId),
                    DotNetNameResolver.typeConverterForShape(specificErrorShapeId, FROM_DAFNY)
            ));
        })).lineSeparated();
        final TokenTree knownErrorsToDafny = TokenTree.of(errorShapes.stream().map(errorShape -> {
            final ShapeId specificErrorShapeId = errorShape.getId();
            return Token.of("if (value is %1$s) return %2$s((%1$s) value);".formatted(
                    nameResolver.baseTypeForShape(specificErrorShapeId),
                    DotNetNameResolver.typeConverterForShape(specificErrorShapeId, TO_DAFNY)
            ));
        })).lineSeparated();
        final TokenTree handleUnknownError = Token.of("throw new System.ArgumentException(\"Unknown exception type\");");

        final TokenTree fromDafnyBody = TokenTree.of(knownErrorsFromDafny, handleUnknownError).lineSeparated();
        final TokenTree fromDafnyConverterSignature = Token.of("public static %s %s(%s value)".formatted(
                cSharpType, DotNetNameResolver.typeConverterForCommonError(serviceShape, FROM_DAFNY), dafnyType));
        final TokenTree fromDafnyConverterMethod = TokenTree.of(fromDafnyConverterSignature, fromDafnyBody.braced());

        final TokenTree toDafnyBody = TokenTree.of(knownErrorsToDafny, handleUnknownError).lineSeparated();
        final TokenTree toDafnyConverterSignature = Token.of("public static %s %s(%s value)".formatted(
                dafnyType, DotNetNameResolver.typeConverterForCommonError(serviceShape, TO_DAFNY), cSharpType));
        final TokenTree toDafnyConverterMethod = TokenTree.of(toDafnyConverterSignature, toDafnyBody.braced());

        // We just need a shape ID that doesn't conflict with anything else
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
                DotNetNameResolver.typeConverterForShape(messageShapeId, FROM_DAFNY)
        ));
        final Token toDafnyBody = Token.of("""
                %1$s converted = new %1$s();
                converted.message = %2$s(value.Message);
                return converted;
                """.formatted(
                        nameResolver.dafnyTypeForShape(errorShape.getId()),
                        DotNetNameResolver.typeConverterForShape(messageShapeId, TO_DAFNY)
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

        final String fromDafnyConverterName = DotNetNameResolver.typeConverterForShape(shape.getId(), FROM_DAFNY);
        final TokenTree fromDafnyConverterSignature = TokenTree.of(
                "public static", cSharpType, fromDafnyConverterName, "(%s value)".formatted(dafnyType));
        final TokenTree fromDafnyConverterMethod = TokenTree.of(fromDafnyConverterSignature, fromDafnyBody.braced());

        final String toDafnyConverterName = DotNetNameResolver.typeConverterForShape(shape.getId(), TO_DAFNY);
        final TokenTree toDafnyConverterSignature = TokenTree.of(
                "public static", dafnyType, toDafnyConverterName, "(%s value)".formatted(cSharpType));
        final TokenTree toDafnyConverterMethod = TokenTree.of(toDafnyConverterSignature, toDafnyBody.braced());

        return new TypeConverter(shape.getId(), fromDafnyConverterMethod, toDafnyConverterMethod);
    }

    @VisibleForTesting
    public Model getModel() {
        return model;
    }
}
