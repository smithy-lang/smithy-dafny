// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydafny;

import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.Token;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.BlobShape;
import software.amazon.smithy.model.shapes.ListShape;
import software.amazon.smithy.model.shapes.MapShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.NumberShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ShapeType;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.LengthTrait;
import software.amazon.smithy.model.traits.RangeTrait;
import software.amazon.smithy.model.traits.TraitDefinition;

import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collection;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.TreeSet;
import java.util.stream.Collectors;

public class DafnyApiCodegen {
    private final Model model;
    private final ServiceShape serviceShape;
    private final DafnyNameResolver nameResolver;

    public DafnyApiCodegen(final Model model, final ShapeId serviceShapeId) {
        this.model = model;
        this.serviceShape = model.expectShape(serviceShapeId, ServiceShape.class);
        this.nameResolver = new DafnyNameResolver(model, serviceShape);
    }

    public Map<Path, TokenTree> generate() {
        final TokenTree includeDirectives = Token.of("""
                include "../StandardLibrary/StandardLibrary.dfy"
                include "../Util/UTF8.dfy"
                """);

        final String serviceName = nameResolver.nameForService();
        final String externNamespace = DafnyNameResolver.dafnyExternNamespaceForShapeId(serviceShape.getId());
        final String moduleName = DafnyNameResolver.dafnyModuleForShapeId(serviceShape.getId());
        final TokenTree moduleHeader = Token.of("module {:extern \"%s\"} %s".formatted(externNamespace, moduleName));

        final TokenTree modulePrelude = Token.of("""
                import opened Wrappers
                import opened StandardLibrary.UInt
                import opened UTF8
                """);
        final TokenTree generatedTypes = TokenTree.of(model.shapes()
                .filter(shape -> ModelUtils.isInServiceNamespace(shape.getId(), serviceShape))
                // Sort by shape ID for deterministic generated code
                .collect(Collectors.toCollection(() -> new TreeSet<>(new ShapeIdComparator())))
                .stream()
                .map(this::generateCodeForShape)
                .flatMap(Optional::stream)
        ).lineSeparated();

        final TokenTree moduleBody = TokenTree.of(modulePrelude, generatedTypes).braced();

        final Path path = Path.of("%s.dfy".formatted(serviceName));
        final TokenTree fullCode = TokenTree.of(includeDirectives, moduleHeader, moduleBody);
        return Map.of(path, fullCode);
    }

    private static class ShapeIdComparator implements Comparator<Shape> {
        @Override
        public int compare(Shape o1, Shape o2) {
            return o1.getId().compareTo(o2.getId());
        }
    }

    private Optional<TokenTree> generateCodeForShape(final Shape shape) {
        final ShapeId shapeId = shape.getId();
        return Optional.ofNullable(switch (shape.getType()) {
            case SERVICE -> {
                if (shape != serviceShape) {
                    throw new IllegalStateException("Unexpected service shape found");
                }
                yield TokenTree.of(generateServiceTraitDefinition(), generateServiceErrorTypeDefinition())
                        .lineSeparated();
            }
            case BLOB -> generateBlobTypeDefinition(shapeId);
            case BOOLEAN -> generateBoolTypeDefinition(shapeId);
            case STRING -> {
                if (shape.hasTrait(EnumTrait.class)) {
                    yield generateEnumTypeDefinition(shapeId);
                } else if (shape.hasTrait(DafnyUtf8BytesTrait.ID)) {
                    yield generateValidUTF8BytesType(shapeId);
                } else {
                    yield generateStringTypeDefinition(shapeId);
                }
            }
            case INTEGER, LONG -> generateNumericTypeDefinition(shapeId);
            case LIST -> generateListTypeDefinition(shapeId);
            case MAP -> generateMapTypeDefinition(shapeId);
            case STRUCTURE -> {
                if (shape.hasTrait(TraitDefinition.class)
                    || shape.hasTrait(ReferenceTrait.class)
                    || shape.hasTrait(PositionalTrait.class)) {
                    yield null;
                } else if (shape.hasTrait(ErrorTrait.class)) {
                    yield generateErrorStructureTypeDefinition(shapeId);
                } else {
                    yield generateStructureTypeDefinition(shapeId);
                }
            }
            default -> null;
        });
    }

    public TokenTree generateValidUTF8BytesType(final ShapeId shapeId) {
        final StringShape stringShape = model.expectShape(shapeId, StringShape.class);
        final Optional<TokenTree> lengthConstraint = stringShape
                .getTrait(LengthTrait.class)
                .map(DafnyApiCodegen::generateLengthConstraint);
        return generateSubsetType(shapeId, "ValidUTF8Bytes", lengthConstraint);
    }

    public TokenTree generateErrorStructureTypeDefinition(final ShapeId shapeId) {
        TokenTree datatype = this.generateStructureTypeDefinition(shapeId);
        StructureShape errorStructure = model.expectShape(shapeId, StructureShape.class);
        final TokenTree castMethod = generateCastToStringForAnErrorStructure(shapeId, errorStructure);
        datatype = datatype.append(castMethod.surround(TokenTree.of("{\n"), TokenTree.of("\n }")));
        return datatype;
    }

    public TokenTree generateCastToStringForAnErrorStructure(final ShapeId shapeId, final StructureShape errorStructure) {
        Optional<MemberShape> message = errorStructure.getMember("message");
        final String castToStringSignature = "\tfunction method CastToString(): string {\n\t%1$s\n\t}";
        String body;
        if (message.isPresent()
                && model.expectShape(message.get().getTarget()).getType() == ShapeType.STRING) {
            body = "\tif message.Some? then \"%1$s: \" + message.value else \"%1$s\"";
        } else {
            body = "\"%1$s\"";
        }
        body = body.formatted(shapeId.getName(serviceShape));
        TokenTree castMethod = TokenTree.of(castToStringSignature.formatted(body));
        return castMethod;
    }

    public TokenTree generateBlobTypeDefinition(final ShapeId blobShapeId) {
        final BlobShape blobShape = model.expectShape(blobShapeId, BlobShape.class);
        final Optional<TokenTree> lengthConstraint = blobShape.getTrait(LengthTrait.class)
                .map(DafnyApiCodegen::generateLengthConstraint);
        return generateSubsetType(blobShapeId, "seq<uint8>", lengthConstraint);
    }

    public TokenTree generateBoolTypeDefinition(final ShapeId boolShapeId) {
        return generateTypeSynonym(boolShapeId, "bool");
    }

    public TokenTree generateStringTypeDefinition(final ShapeId stringShapeId) {
        final StringShape stringShape = model.expectShape(stringShapeId, StringShape.class);
        final Optional<TokenTree> lengthConstraint = stringShape.getTrait(LengthTrait.class)
                .map(DafnyApiCodegen::generateLengthConstraint);
        return generateSubsetType(stringShapeId, "string", lengthConstraint);
    }

    public TokenTree generateEnumTypeDefinition(final ShapeId stringShapeId) {
        final StringShape stringShape = model.expectShape(stringShapeId, StringShape.class);
        final EnumTrait enumTrait = stringShape.getTrait(EnumTrait.class).orElseThrow();

        if (!enumTrait.hasNames()) {
            throw new UnsupportedOperationException("Unnamed enums not supported");
        }
        //noinspection OptionalGetWithoutIsPresent
        final TokenTree constructors = TokenTree.of(enumTrait.getValues().stream()
                .map(enumDefinition -> enumDefinition.getName().get())
                .peek(name -> {
                    if (!ModelUtils.isValidEnumDefinitionName(name)) {
                        throw new UnsupportedOperationException("Invalid enum definition name: %s".formatted(name));
                    }
                })
                .map(name -> TokenTree.of("\n\t|", name)));

        return Token.of("datatype %s =".formatted(nameResolver.baseTypeForShape(stringShapeId))).append(constructors);
    }

    public TokenTree generateNumericTypeDefinition(final ShapeId numberShapeId) {
        final NumberShape numberShape = model.expectShape(numberShapeId, NumberShape.class);
        final Optional<TokenTree> rangeConstraint = numberShape.getTrait(RangeTrait.class)
                .map(DafnyApiCodegen::generateRangeConstraint);
        final String baseType = Objects.requireNonNull(
                DafnyNameResolver.DAFNY_TYPES_BY_SIMPLE_SHAPE_TYPE.get(numberShape.getType()));
        return generateSubsetType(numberShapeId, baseType, rangeConstraint);
    }

    public TokenTree generateListTypeDefinition(final ShapeId listShapeId) {
        final ListShape listShape = model.expectShape(listShapeId, ListShape.class);
        final Optional<TokenTree> lengthConstraint = listShape.getTrait(LengthTrait.class)
                .map(DafnyApiCodegen::generateLengthConstraint);
        final String baseType = "seq<%s>".formatted(nameResolver.baseTypeForShape(listShape.getMember().getId()));
        return generateSubsetType(listShapeId, baseType, lengthConstraint);
    }

    public TokenTree generateMapTypeDefinition(final ShapeId mapShapeId) {
        final MapShape mapShape = model.expectShape(mapShapeId, MapShape.class);
        final Optional<TokenTree> lengthConstraint = mapShape.getTrait(LengthTrait.class)
                .map(DafnyApiCodegen::generateLengthConstraint);
        final String keyType = nameResolver.baseTypeForShape(mapShape.getKey().getId());
        final String valueType = nameResolver.baseTypeForShape(mapShape.getValue().getId());
        final String baseType = "map<%s, %s>".formatted(keyType, valueType);
        return generateSubsetType(mapShapeId, baseType, lengthConstraint);
    }

    public TokenTree generateStructureTypeDefinition(final ShapeId structureShapeId) {
        final StructureShape structureShape = model.expectShape(structureShapeId, StructureShape.class);
        final TokenTree params = TokenTree.of(ModelUtils.streamStructureMembers(structureShape)
                .map(this::generateStructureTypeParameter)
        ).separated(Token.of(",")).parenthesized();

        final String typeName = structureShapeId.getName(serviceShape);
        return TokenTree.of(
                Token.of("datatype %1$s = %1$s".formatted(typeName)),
                params);
    }

    private TokenTree generateStructureTypeParameter(final MemberShape memberShape) {
        return Token.of("\n\tnameonly %s: %s".formatted(
                memberShape.getMemberName(), nameResolver.baseTypeForShape(memberShape.getId())));
    }

    public TokenTree generateServiceTraitDefinition() {
        final TokenTree trait = TokenTree.of("trait", nameResolver.traitForServiceClient(serviceShape));
        final TokenTree predicatesAndMethods = TokenTree.of(
                serviceShape.getAllOperations().stream().map(this::generateOperationPredicatesAndMethod))
                .lineSeparated();
        return TokenTree.of(trait, predicatesAndMethods.braced());
    }

    public TokenTree generateOperationPredicatesAndMethod(final ShapeId operationShapeId) {

        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);
        final TokenTree operationParams = operationShape.getInput()
                .map(nameResolver::baseTypeForShape)
                .map(inputType -> TokenTree.of("input:", inputType))
                .orElse(TokenTree.empty())
                ;
        final Optional<String> outputType = this.nameResolver.returnTypeForResult(operationShape);
        TokenTree returnType = TokenTree.empty();
        if (outputType.isPresent()) {
            returnType = TokenTree.of("output: %s".formatted(outputType.get()));
        }

        final TokenTree wrappedReply = Token.of("output: %s"
                .formatted(nameResolver.returnTypeForOperation(operationShape)));
        final TokenTree calledWithPredicate = this.generatePredicateCalledWith(operationShape, operationParams);
        final TokenTree succeededWithPredicate = this.generatePredicateSucceededWith(operationShape, operationParams, returnType);
        final TokenTree method = this.generateOperationMethod(operationShape, operationParams, wrappedReply);

        return TokenTree.of(calledWithPredicate, succeededWithPredicate, method).lineSeparated().append(TokenTree.of("\n"));
    }

    private TokenTree generateOperationMethod(
            final OperationShape operationShape,
            final TokenTree operationParams,
            final TokenTree wrappedReply
    ) {
        final TokenTree name = TokenTree.of("method", nameResolver.methodForOperation(operationShape));
        final TokenTree params = operationParams.parenthesized();
        final TokenTree returns = TokenTree.of("returns ").append(wrappedReply.parenthesized());

        // The formal Dafny name for this section of a method is "specification".
        // To avoid confusion with RFC-style "specifications", instead use the term "conditions".
        TokenTree conditions = TokenTree.empty();

        TokenTree ensureCalledWith = TokenTree.of(
                "\n\tensures "
                        + nameResolver.predicateCalledWith(operationShape)
        );
        TokenTree ensureSucceededWith = TokenTree.of(
                "\n\tensures output.Success? ==> "
                        + nameResolver.predicateSucceededWith(operationShape)
        );
        TokenTree ensureCalledWithParams = TokenTree.empty();
        TokenTree ensureSucceededWithParams = TokenTree.empty();
        if (operationShape.getInput().isPresent()) {
            ensureCalledWithParams = ensureCalledWithParams.append(TokenTree.of("input"));
            ensureSucceededWithParams = ensureSucceededWithParams.append(TokenTree.of("input"));
        }
        if (operationShape.getInput().isPresent() && operationShape.getOutput().isPresent()) {
            ensureSucceededWithParams = ensureSucceededWithParams.append(TokenTree.of(","));
        }
        if (operationShape.getOutput().isPresent()) {
            ensureSucceededWithParams = ensureSucceededWithParams.append(TokenTree.of("output.value"));
        }
        ensureCalledWithParams = ensureCalledWithParams.parenthesized();
        ensureSucceededWithParams = ensureSucceededWithParams.parenthesized();

        ensureCalledWith = ensureCalledWith.append(ensureCalledWithParams);
        ensureSucceededWith = ensureSucceededWith.append(ensureSucceededWithParams);
        conditions = conditions.append(ensureCalledWith);
        conditions = conditions.append(ensureSucceededWith);
        return TokenTree.of(name, params, returns, conditions);
    }

    private TokenTree generatePredicateCalledWith(
            final OperationShape operationShape,
            final TokenTree operationParams
    ) {
        final TokenTree name = TokenTree.of("predicate {:opaque}", nameResolver.predicateCalledWith(operationShape));
        TokenTree params = TokenTree.of("(");
        if (operationShape.getInput().isPresent()) {
            params = TokenTree.of(params, operationParams);
        }
        params = params.append(TokenTree.of(")"));
        final TokenTree body = TokenTree.of("{true}");
        return TokenTree.of(name, params, body);
    }

    private TokenTree generatePredicateSucceededWith(
            final OperationShape operationShape,
            final TokenTree operationParams,
            final TokenTree returnType
    ) {
        TokenTree params = TokenTree.empty();
        if (operationShape.getInput().isPresent()) {
            params = TokenTree.of(params, operationParams);
        }
        if (operationShape.getInput().isPresent() && operationShape.getOutput().isPresent()) {
            params = params.append(TokenTree.of(","));
        }
        if (operationShape.getOutput().isPresent()) {
            params = params.append(returnType);
        }
        params = params.parenthesized();
        final TokenTree name = TokenTree.of("predicate {:opaque}", nameResolver.predicateSucceededWith(operationShape));
        final TokenTree body = TokenTree.of("{true}");
        return TokenTree.of(name, params, body);
    }

    /**
     * Generates a sum type for the error shapes of operations in the service.
     */
     // TODO: once traits can be used as type parameters, make this a trait instead so that we don't
     // need to exhaustively specify the error shapes of operations
    public TokenTree generateServiceErrorTypeDefinition() {
        // Collect into TreeSet so that the error shapes are lexicographically sorted, ordering them deterministically
        final TreeSet<ShapeId> errorShapeIds = ModelUtils.streamServiceErrors(model, serviceShape)
                .map(Shape::getId)
                .collect(Collectors.toCollection(TreeSet::new));

        final TokenTree unknownConstructor = Token.of("| %s(unknownMessage: string)".formatted(
                nameResolver.nameForServiceErrorUnknownConstructor(serviceShape)));
        final TokenTree knownConstructors = TokenTree.of(errorShapeIds.stream()
                .map(errorShapeId -> Token.of("| %1$s(%2$s: %2$s)".formatted(
                    nameResolver.nameForServiceErrorConstructor(errorShapeId), nameResolver.baseTypeForShape(errorShapeId)))))
                .lineSeparated();
        final TokenTree allConstructors = TokenTree.of(unknownConstructor, knownConstructors).lineSeparated();
        TokenTree serviceErrorDatatype = TokenTree.of("datatype", nameResolver.errorTypeForService(serviceShape), "=\n")
                .append(allConstructors);

        return serviceErrorDatatype
                .append(generateCastToStringForErrorStructure(errorShapeIds))
                .lineSeparated();
    }

    /**
     * Generates a function method to cast all subtypes of generated Service Error
     * to a string.
     */
    public TokenTree generateCastToStringForErrorStructure(final TreeSet<ShapeId> errorShapeIds) {
        String castToStringFunctionMethodName = "Cast"
                + nameResolver.errorTypeForService(serviceShape)
                + "ToString";
        TokenTree castToStringSignature = TokenTree.of("function method %1$s(error: %2$s): string".formatted(
                castToStringFunctionMethodName, nameResolver.errorTypeForService(serviceShape)));
        final String commonCaseBody = "\n\tcase %1$s(arg) => arg.CastToString()";
        final TokenTree body = TokenTree.of(errorShapeIds.stream()
                        .map(errorShapeId -> TokenTree.of(commonCaseBody.formatted(
                                nameResolver.nameForServiceErrorConstructor(errorShapeId)))))
                .surround(
                        TokenTree.of("\tmatch error"),
                        TokenTree.of("\n\tcase %1$s(arg) => \"Unexpected Exception from AWS %2$s: \" + arg".formatted(
                                nameResolver.nameForServiceErrorUnknownConstructor(serviceShape),
                                nameResolver.nameForService())))
                .braced();
        return castToStringSignature.append(body);
    }

    private static TokenTree generateLengthConstraint(final LengthTrait lengthTrait) {
        final String min = lengthTrait.getMin().map("%s <="::formatted).orElse("");
        final String max = lengthTrait.getMax().map("<= %s"::formatted).orElse("");
        return TokenTree.of(min, "|x|", max);
    }

    private static TokenTree generateRangeConstraint(final RangeTrait rangeTrait) {
        final String min = rangeTrait.getMin().map("%s <="::formatted).orElse("");
        final String max = rangeTrait.getMax().map("<= %s"::formatted).orElse("");
        return TokenTree.of(min, "x", max);
    }

    /**
     * Given a name {@code TypeName}, base type {@code BaseType}, and constraint predicate expressions
     * {@code c1, c2, ..., cN} over a free variable {@code x}, generates a subset type like
     * <pre>
     * type TypeName = x: BaseType | (c1) && (c2) && ... && (cN) witness *
     * </pre>
     *
     * If no constraint expressions are provided, then instead generates a type synonym like
     * <pre>
     * type TypeName = BaseType
     * </pre>
     */
    private TokenTree generateSubsetType(
            final ShapeId shapeId, final String baseType, final Collection<TokenTree> constraints) {
        final String typeName = nameResolver.generatedTypeForShape(shapeId);
        if (constraints.size() == 0) {
            return TokenTree.of("type", typeName, "=", baseType);
        }

        final TokenTree constraintsConjunct = TokenTree.of(constraints.stream().map(TokenTree::parenthesized))
                .separated(Token.of("&&"));
        final String validityPredicateName = nameResolver.validityPredicateForShape(shapeId);
        final TokenTree validityPredicate = Token.of(
                "predicate method %s(x: %s)".formatted(validityPredicateName, baseType))
                .append(constraintsConjunct.braced());
        final TokenTree subsetType =
                Token.of("type %s = x: %s | %s(x) witness *".formatted(typeName, baseType, validityPredicateName));

        return TokenTree.of(subsetType, validityPredicate).lineSeparated();
    }

    /**
     * Like {@link DafnyApiCodegen#generateSubsetType(ShapeId, String, Collection<TokenTree>)}, but accepts
     * {@link Optional}-wrapped constraints and discards the empty ones.
     */
    @SuppressWarnings("JavaDoc")
    @SafeVarargs
    private TokenTree generateSubsetType(
            final ShapeId shapeId, final String baseType, final Optional<TokenTree>... constraintOptionals) {
        final List<TokenTree> constraints = Arrays.stream(constraintOptionals).flatMap(Optional::stream).toList();
        return generateSubsetType(shapeId, baseType, constraints);
    }

    @SuppressWarnings("SameParameterValue")
    private TokenTree generateTypeSynonym(
            final ShapeId shapeId, final String baseType) {
        return generateSubsetType(shapeId, baseType, Optional.empty());
    }
}
