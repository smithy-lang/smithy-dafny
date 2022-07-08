// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydafny;

import com.google.common.annotations.VisibleForTesting;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.Token;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.*;
import software.amazon.smithy.model.traits.*;
import software.amazon.smithy.aws.traits.*;

import java.nio.file.Path;
import java.util.*;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class DafnyApiCodegen {
    private final Model model;
    private final ServiceShape serviceShape;
    private final DafnyNameResolver nameResolver;
    private final Path modelPath;

    public DafnyApiCodegen(
      final Model model,
      final ServiceShape serviceShape,
      final Path modelPath,
      final Path[] dependentModelPaths
    ) {
        this.model = model;
        this.serviceShape = serviceShape;
        this.modelPath = modelPath;
        this.nameResolver = new DafnyNameResolver(
          model,
          this.serviceShape.toShapeId().getNamespace(),
          new HashSet(),
          dependentModelPaths.clone()
        );
    }

    public Map<Path, TokenTree> generate() {

        // I generate the types *first*
        // This is because the generated types
        // MAY depend on other models.
        // In this case I need these modules
        // so that I can include them.
        final TokenTree generatedTypes = TokenTree
          .of(
            model
              .shapes()
              .filter(shape -> ModelUtils.isInServiceNamespace(shape.getId(), serviceShape))
              // Sort by shape ID for deterministic generated code
              .collect(Collectors.toCollection(TreeSet::new))
              .stream()
              .map(this::generateCodeForShape)
              .flatMap(Optional::stream)
            )
          .lineSeparated();

        // A smithy model may reference a model in a different package.
        // In which case we need to include it.
        final TokenTree includeDirectives = TokenTree
          .of(Stream
            .concat(
              Stream
                .of(
                  // These are Obviously wrong #JustHardCodedThings...
                  "../../StandardLibrary/StandardLibrary.dfy",
                  "../../Util/UTF8.dfy"
                ),
              nameResolver
                .dependentModels()
                .stream()
                .map(d -> modelPath
                  .relativize(d.modelPath().resolve(nameResolver.dafnyTypesModuleForNamespace(d.namespace()) + ".dfy"))
                )
                .map(Path::toString)
            )
            .map(p -> "include \"" + p + "\"")
            .map(Token::of)
          )
          .lineSeparated();

        final String namespace = serviceShape.getId().getNamespace();
        final String typesModuleName = DafnyNameResolver.dafnyTypesModuleForNamespace(namespace);
        final TokenTree typesModuleHeader = Token.of("module {:extern \"%s\" } %s"
          .formatted(
            DafnyNameResolver.dafnyExternNamespaceForShapeId(serviceShape.getId()),
            typesModuleName
          ));

        // A smithy model may reference a model in a different package.
        // In which case we need to import it.
        final TokenTree typesModulePrelude = TokenTree
          .of(Stream
            .concat(
                Stream
                .of(
                  "import opened Wrappers",
                  "import opened StandardLibrary.UInt",
                  "import opened UTF8"
                ),
              nameResolver
                .dependentModels()
                .stream()
                .map(d ->
                  "import " + nameResolver.dafnyTypesModuleForNamespace(d.namespace())))
            .map(i -> Token.of(i)))
          .lineSeparated();

        final TokenTree typesModuleBody = TokenTree
            .of(
              typesModulePrelude,
              // These are just put here to facilitate nice formatting...
              TokenTree.of("// Generic helpers for verification of mock/unit tests."),
              TokenTree.of("datatype %s<I, O> = %s(input: I, output: O)"
                .formatted(
                  nameResolver.callEventTypeName(),
                  nameResolver.callEventTypeName()
                )),
              TokenTree.of("function Last<T>(s: seq<T>): T requires |s| > 0 { s[|s|-1] }"),
              TokenTree.empty(),
              TokenTree.of("// Begin Generated Types"),
              TokenTree.empty(),
              generatedTypes,
              // Error types are generates *after*
              // all other types to account
              // for any dependant modules
              generateModeledErrorDataType()
            )
            .lineSeparated()
            .braced();


      final String abstractModuleName = DafnyNameResolver
        .dafnyAbstractModuleForNamespace(serviceShape.getId().getNamespace());
      final TokenTree abstractModuleHeader = Token.of("abstract module %s".formatted(abstractModuleName));

      final TokenTree abstractModuleBody = TokenTree
        .of(generateAbstractBody())
        .lineSeparated()
        .braced();

        final Path path = Path.of("%s.dfy".formatted(typesModuleName));
        final TokenTree fullCode = TokenTree
          .of(
            includeDirectives,
            typesModuleHeader, typesModuleBody,
            abstractModuleHeader, abstractModuleBody
          )
          .lineSeparated();
        return Map.of(path, fullCode);
    }

    private Optional<TokenTree> generateCodeForShape(final Shape shape) {
        final ShapeId shapeId = shape.getId();
        return Optional.ofNullable(switch (shape.getType()) {
            case SERVICE -> TokenTree
                  .of(generateServiceTraitDefinition(serviceShape))
                  .lineSeparated();
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
                if (shape.hasTrait(TraitDefinition.class)) {
                    yield null;
                } else if (shape.hasTrait(PositionalTrait.class)) {
                    yield null;
                } else if (shape.hasTrait(ReferenceTrait.class)) {
                    yield generateReferenceTraitDefinition(shapeId);
                } else if (shape.hasTrait(ErrorTrait.class)) {
                    // All error shapes are a single integrated data type
                    yield null;
                } else {
                    yield generateStructureTypeDefinition(shapeId);
                }
            }
            case UNION -> generateUnionTypeDefinition(shapeId);
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

        final String typeName = structureShapeId.getName();
        return TokenTree.of(
          Token.of("datatype %1$s =".formatted(typeName)),
          generateDataTypeConstructorFromStructure(structureShapeId)
        );
    }

    public TokenTree generateUnionTypeDefinition(final ShapeId unionShapeId) {
        final UnionShape unionShape = model.expectShape(unionShapeId, UnionShape.class);

        return TokenTree.of(
          Token.of("datatype %s =".formatted(nameResolver.baseTypeForShape(unionShapeId))),
          TokenTree.of(
            unionShape
              .members()
              .stream()
              .map(this::generateWrappedDataTypeConstructorFromUnionMember)).lineSeparated()
          ).lineSeparated();
    }

    public TokenTree generateWrappedDataTypeConstructorFromUnionMember(final MemberShape memberShape) {
        final String name = memberShape.getMemberName();
        final String wrappedType = nameResolver.baseTypeForShape(memberShape.getTarget());

        return TokenTree.of(
          "| %s(%s: %s)".formatted(name, wrappedType.replace(".", ""), wrappedType)
        );
    }

    private TokenTree generateStructureTypeParameter(final MemberShape memberShape) {
        return Token.of("nameonly %s: %s".formatted(
                memberShape.getMemberName(), nameResolver.baseTypeForShape(memberShape.getId())));
    }

    public TokenTree generateServiceTraitDefinition(ServiceShape serviceShape) {

        final TokenTree trait = TokenTree
          .of(
            "trait {:termination false}",
            nameResolver.traitForServiceClient(serviceShape)
          );
        // See generateOperationPredicatesAndMethod, when updated, change me back
        final TokenTree methods = TokenTree
          .of(
            serviceShape
              .getAllOperations()
              .stream()
              .flatMap(operation -> Stream.of(
                generateBodilessOperationMethodThatEnsuresCallEvents(serviceShape, operation),
                TokenTree.empty()
                )
              )
          )
          .lineSeparated();

        return TokenTree
          .of(
            trait,
            methods.braced()
          )
          .lineSeparated();
    }
    
    public TokenTree generateReferenceTraitDefinition(final ShapeId shapeWithReference) {
        final ReferenceTrait referenceTrait = model
          .getShape(shapeWithReference)
          .orElseThrow()
          .expectTrait(ReferenceTrait.class);

        // This is a reference structure for returning a service
        // As such, there is no need to build any code here.
        // The actual implementation of the service
        // would be in that services Smithy module.
        if (referenceTrait.isService()) {
            return null;
        }

        final ResourceShape resource = model
          .getShape(referenceTrait.getReferentId())
          .orElseThrow()
          .asResourceShape()
          .orElseThrow();
    
        final TokenTree trait = TokenTree
          .of(
            "trait {:termination false}",
            nameResolver.baseTypeForShape(shapeWithReference)
          );

        final TokenTree methods = TokenTree
          .of(
            resource
              .getAllOperations()
              .stream()
              .flatMap(operation -> Stream.of(
                generateResourceOperationMethod(serviceShape, operation),
                TokenTree.empty()
              ))
          )
          .lineSeparated();

        return TokenTree
          .of(
            trait,
            methods.braced()
          )
          .lineSeparated();
    }

    public TokenTree generateOperationParams(final OperationShape operationShape) {
        return operationShape
          .getInput()
          .map(nameResolver::baseTypeForShape)
          .map(inputType -> TokenTree.of("input:", inputType))
          .orElse(TokenTree.empty());
    }

    private TokenTree generateOperationOutputParams(final OperationShape operationShape) {
        return TokenTree
          .of("output: %s".formatted(nameResolver.returnTypeForOperation(operationShape)));
    }

    private TokenTree generateOperationReturnsClause(
      final ServiceShape serviceShape,
      final OperationShape operationShape
    ) {
        return TokenTree
          .of("%s (%s)"
            .formatted(
              nameResolver.isFunction(serviceShape, operationShape)
                ? ":"
                : "returns",
              generateOperationOutputParams(operationShape)
            ));
    }

    private TokenTree generateBodilessOperationMethodThatEnsuresCallEvents(
      final ServiceShape serviceShape,
      final ShapeId operationShapeId
    ) {
      final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);

      final Boolean isFunction = nameResolver.isFunction(serviceShape, operationShape);

      final TokenTree publicOperationMethod = TokenTree
        .of(
          TokenTree
            .of(nameResolver.executableType(serviceShape, operationShape))
            .append(Token.of(nameResolver.publicMethodNameForOperation(operationShape)))
            .append(generateOperationParams(operationShape).parenthesized()),
          generateOperationReturnsClause(serviceShape, operationShape),
          isFunction
            ? TokenTree.of("// Functions that are transparent do not need ensures")
            : TokenTree
            .of(
              generateModifiesHistoricalCallEvents(operationShapeId),
              generateEnsuresForEnsuresPubliclyPredicate(operationShapeId),
              generateEnsuresHistoricalCallEvents(operationShapeId)
            )
            .lineSeparated()
        )
        .lineSeparated();
      return TokenTree
        .of(
          isFunction
            ? TokenTree
            .of("// Functions are deterministic, no need for historical call events or ensures indirection")
            : TokenTree
            .of(
              generateHistoricalCallEvents(operationShapeId),
              generateEnsuresPubliclyPredicate(operationShapeId)
            )
            .lineSeparated(),
          // This function returns the bodiless method
          // at the end of the TokenTree
          // so that other callers can compose
          // and add bodies.
          TokenTree.of("// The public method to be called by library consumers"),
          publicOperationMethod
        )
        .lineSeparated();
    }
    private TokenTree generateResourceOperationMethod(
      final ServiceShape serviceShape,
      final ShapeId operationShapeId
    ) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);

        return TokenTree
          .of(
            generateBodilessOperationMethodThatEnsuresCallEvents(serviceShape, operationShapeId),
            // Implement this for library developer
            // This implementation will record the call outcome
            // and return the result
            TokenTree
              .of(
                TokenTree
                  .of("output :=")
                  .append(Token.of(nameResolver.methodNameToImplementForResourceOperation(operationShape)))
                  .append(TokenTree.of("(input);")),
                generateAccumulateHistoricalCallEvents(operationShapeId)
              )
              .lineSeparated()
              .braced(),
            // This is method for the library developer to implement
            TokenTree
              .of(
                TokenTree.of("// The method to implement in the concrete class. "),
                TokenTree
                  .of(nameResolver.executableType(serviceShape, operationShape))
                  .append(Token.of(nameResolver.methodNameToImplementForResourceOperation(operationShape)))
                  .append(generateOperationParams(operationShape).parenthesized()),
                generateOperationReturnsClause(serviceShape, operationShape),
                generateEnsuresForEnsuresPubliclyPredicate(operationShapeId)
              )
              .lineSeparated()
          )
          .lineSeparated();
    }

    private TokenTree generatePredicateCalledWith(
      final ShapeId thisShape,
      final ShapeId operationShapeId
    ) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);
        final String name = nameResolver.predicateCalledWith(operationShape);

        final String thisType = nameResolver.baseTypeForShape(thisShape);

        // First get the parameters
        final TokenTree params = generateOperationParams(operationShape)
          .append(TokenTree.of("obj:%s,".formatted(thisType)))
          .parenthesized();

        // Build the predicate that can be used as a simple mock
        final TokenTree predicate = TokenTree
          .of(
            Token.of("predicate {:axiom}"),
            Token.of(name),
            params // Without a body. This way it can not be assumed or revealed
          );

        // A lemma that is used to ensure the bodiless predicate above
        final TokenTree lemma = TokenTree
          .of(
            Token.of("lemma {:axiom}"),
            Token.of("Assume%s".formatted(name)),
            params,
            Token.NEWLINE,
            Token.of("ensures"),
            Token.of(name),
            // Simplify? Need to call the predicate
            operationShape
              .getInput()
              // This can be hard coded because we are calling "getInput"
              .map(member ->  TokenTree.of("input"))
              .orElse(TokenTree.empty())
              .parenthesized()
          );

        return TokenTree
          .of(predicate, lemma)
          .lineSeparated();
    }




    private TokenTree generatePredicates(
      final ShapeId thisShape,
      final ShapeId operationShapeId
    ) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);
        final String thisType = nameResolver.baseTypeForShape(thisShape);

        // First get the parameters
        final TokenTree baseParams = generateOperationParams(operationShape)
          .prepend(TokenTree.of("obj:%s,".formatted(thisType)));

        final TokenTree calledParameters = baseParams.parenthesized();

        final TokenTree succeededWithParameters = TokenTree
          .of(
            baseParams,
            operationShape
              .getOutput()
              .map(nameResolver::baseTypeForShape)
              .map(outputType -> TokenTree.of("," ,"output:", outputType))
              .orElse(TokenTree.empty())
          )
          .parenthesized();

        final TokenTree failedWithParameters = TokenTree
          .of(
            baseParams,
            TokenTree.of("," ,"error: Error")
          )
          .parenthesized();

        final TokenTree predicates = TokenTree.of(
          Stream.of(
            new AbstractMap.SimpleEntry<String, TokenTree>(
              nameResolver.predicateCalledWith(operationShape),
              calledParameters),
            new AbstractMap.SimpleEntry<String, TokenTree>(
              nameResolver.predicateSucceededWith(operationShape),
              succeededWithParameters),
            new AbstractMap.SimpleEntry<String, TokenTree>(
              nameResolver.predicateFailed(operationShape),
              calledParameters),
            new AbstractMap.SimpleEntry<String, TokenTree>(
              nameResolver.predicateFailedWith(operationShape),
              failedWithParameters)
          )
          .map(pair -> TokenTree
            .of(
              Token.of("predicate {:axiom}"),
              Token.of(pair.getKey()),
              pair.getValue() // Without a body. This way it can not be assumed or revealed
            )
          ))
          .lineSeparated();

        final TokenTree lemmaEnsures = generateEnsuresMockInformation(operationShapeId, "obj");
        final TokenTree lemmaParams = TokenTree
          .of(
            baseParams,
            TokenTree.of("output:%s".formatted(nameResolver.returnTypeForOperation(operationShape)))
          )
          .separated(Token.of(","))
          .parenthesized();

        // A lemma that is used to ensure the bodiless predicate above
        final TokenTree lemma = TokenTree
          .of(
            Token.of("lemma {:axiom} Assume%s".formatted(operationShape.getId().getName())),
            lemmaParams,
            lemmaEnsures
          )
          .lineSeparated();

        return TokenTree
          .of(predicates, lemma)
          .lineSeparated();
    }


    private  TokenTree generateHistoricalCallEvents(
      final ShapeId operationShapeId
    ) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);
        // The Dafny datatype OR unit ()
        final String inputType = operationShape
          .getInput()
          .map(nameResolver::baseTypeForShape)
          .orElse("()");
        final String outputType = nameResolver.returnTypeForOperation(operationShape);

        return TokenTree
          .of(
            "ghost var %s: seq<%s<%s, %s>>"
              .formatted(
                nameResolver.historicalCallEventsForOperation(operationShape),
                nameResolver.callEventTypeName(),
                inputType,
                outputType
              )
          );
    }

    private TokenTree generateModifiesHistoricalCallEvents(
      final ShapeId operationShapeId
    ) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);
        return TokenTree
          .of(
            "modifies this`%s"
              .formatted(nameResolver.historicalCallEventsForOperation(operationShape))
          );
    }

    private TokenTree generateEnsuresHistoricalCallEvents(
        final ShapeId operationShapeId
    ) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);

        final String historicalCallEventsForOperation = nameResolver.historicalCallEventsForOperation(operationShape);

        return TokenTree
          .of(
            Token.of("ensures"),
            Token.of("&& 0 < |%s|".formatted(historicalCallEventsForOperation)),
            Token.of("&& Last(%s) == %s(input, output)"
              .formatted(
                historicalCallEventsForOperation,
                nameResolver.callEventTypeName()
              ))
          )
          .lineSeparated();
    }

    private TokenTree generateAccumulateHistoricalCallEvents(
      final ShapeId operationShapeId
    ) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);
        final String historicalCallEvents = nameResolver.historicalCallEventsForOperation(operationShape);
        return TokenTree
          .of(
            "%s := %s + [%s(input, output)];"
              .formatted(
                historicalCallEvents,
                historicalCallEvents,
                nameResolver.callEventTypeName()
              )
          );
    }

    private TokenTree generateEnsuresPubliclyPredicate(
      final ShapeId operationShapeId
    ) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);

        return TokenTree
          .of(
            "predicate %s(%s, %s)"
              .formatted(
                nameResolver.ensuresPubliclyPredicate(operationShape),
                generateOperationParams(operationShape),
                generateOperationOutputParams(operationShape)
              )
          );
    }

    private TokenTree generateEnsuresForEnsuresPubliclyPredicate(
      final ShapeId operationShapeId
    ) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);

        return TokenTree
          .of(
            "ensures %s(input, output)".formatted(nameResolver.ensuresPubliclyPredicate(operationShape))
          );
    }

    private TokenTree generateEnsuresMockInformation(
      final ShapeId operationShapeId,
      final String thisObjName
    ) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);

        final String calledName = nameResolver.predicateCalledWith(operationShape);
        final String succeededWithName = nameResolver.predicateSucceededWith(operationShape);
        final String failedName = nameResolver.predicateFailed(operationShape);
        final String failedWithName = nameResolver.predicateFailedWith(operationShape);

        return TokenTree
          .of(
            Token.of("ensures"),
            Token.of("&& %s( %s, input )".formatted(calledName, thisObjName)),
            Token.of("&& if output.Success? then"),
            Token.of("&& %s( %s, input %s )"
              .formatted(
                succeededWithName,
                thisObjName,
                operationShape.getOutput().isPresent()
                  ? ", output.value"
                  : ""
              )),
            Token.of("&& !%s( %s, input )".formatted(failedName, thisObjName)),
            Token.of("else"),
            Token.of("&& output.Failure?"),
            Token.of("&& %s( %s, input )".formatted(failedName, thisObjName)),
            Token.of("&& %s( %s, input, output.error )".formatted(failedWithName, thisObjName))
          )
          .lineSeparated();
    }

    private TokenTree generatePredicateSucceededWith(
      final ShapeId operationShapeId
    ) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);
        final String name = nameResolver.predicateSucceededWith(operationShape);

        // Build the parameters. Need input and output
        final TokenTree params = TokenTree
          .of(
            generateOperationParams(operationShape),
            operationShape
              .getOutput()
              .map(nameResolver::baseTypeForShape)
              .map(outputType -> TokenTree.of("," ,"output:", outputType))
              .orElse(TokenTree.empty())
          )
          .parenthesized();

        // Build the predicate that can be used as a simple mock
        final TokenTree predicate = TokenTree
          .of(
            Token.of("predicate {:axiom}"),
            Token.of(name),
            params  // Without a body. This way it can not be assumed or revealed
          );

        // A lemma that is used to ensure the bodiless predicate above
        final TokenTree lemma = TokenTree
          .of(
            Token.of("lemma {:axiom}"),
            Token.of("Assume%s".formatted(name)),
            params,
            Token.NEWLINE,
            Token.of("ensures"),
            Token.of(name),
            // Simplify? Need to call the predicate
            TokenTree
              .of(
                operationShape
                  .getInput()
                  // This can be hard coded because we are calling "getInput"
                  .map(member ->  TokenTree.of("input"))
                  .orElse(TokenTree.empty()),
                operationShape
                  .getOutput()
                  // This can be hard coded because we are calling "getInput"
                  .map(member ->  TokenTree.of(",", "output"))
                  .orElse(TokenTree.empty())
              )
              .parenthesized()
          );

        return TokenTree
          .of(predicate, lemma)
          .lineSeparated();
    }


    /**
     * Generates the service's error types that are not modeled directly. These include:
     * <ul>
     *     <li>the error trait</li>
     *     <li>an "unknown error" class</li>
     * </ul>
     */
    public TokenTree generateModeledErrorDataType() {
        return TokenTree.of(
          Token.of("datatype Error ="),
          Token.of("// Local Error structures are listed here"),
          TokenTree.of(
            ModelUtils
              .streamNamespaceErrors(model, serviceShape.getId().getNamespace())
              .map(Shape::getId)
              .map(this::generateDataTypeConstructorFromStructure)
          ).lineSeparated(),
          Token.of("// Any dependent models are listed here"),
          TokenTree.of(
            nameResolver
              .dependentModels()
              .stream()
              .map(this::generateDependantErrorDataTypeConstructor)
          ).lineSeparated(),
          Token.of("// The Collection error is used to collect several errors together"),
          Token.of("// This is useful when composing OR logic."),
          Token.of("// Consider the following method:"),
          Token.of("// "),
          Token.of("// method FN<I, O>(n:I)"),
          Token.of("//   returns (res: Result<O, Types.Error>)"),
          Token.of("//   ensures A(I).Success? ==> res.Success?"),
          Token.of("//   ensures B(I).Success? ==> res.Success?"),
          Token.of("//   ensures A(I).Failure? && B(I).Failure? ==> res.Failure?"),
          Token.of("// "),
          Token.of("// If either A || B is successful then FN is successful."),
          Token.of("// And if A && B fail then FN will fail."),
          Token.of("// But what information should FN transmit back to the caller?"),
          Token.of("// While it may be correct to hide these details from the caller,"),
          Token.of("// this can not be the globally correct option."),
          Token.of("// Suppose that A and B can be blocked by different ACLs,"),
          Token.of("// and that their representation of I is only eventually consistent."),
          Token.of("// How can the caller distinguish, at a minimum for logging,"),
          Token.of("// the difference between the four failure modes?"),
          Token.of("// || (!access(A(I)) && !access(B(I)))"),
          Token.of("// || (!exit(A(I)) && !exit(B(I)))"),
          Token.of("// || (!access(A(I)) && !exit(B(I)))"),
          Token.of("// || (!exit(A(I)) && !access(B(I)))"),
          Token.of("| Collection(list: seq<Error>)"),
          Token.of("// The Opaque error, used for native, extern, wrapped or unknown errors"),
          Token.of("| Opaque(obj: object)"),
          // Helper error for use with `extern`
          Token.of("type OpaqueError = e: Error | e.Opaque? witness *")
        ).lineSeparated();
    }

    public TokenTree generateDataTypeConstructorFromStructure(final ShapeId shapeId) {
        final StructureShape structureShape = model.expectShape(shapeId, StructureShape.class);
        final String typeName = shapeId.getName();

        final TokenTree params = TokenTree
          .of(ModelUtils
            .streamStructureMembers(structureShape)
            .map(this::generateStructureTypeParameter)
          )
          // This combines the trees
          .separated(TokenTree.of(Token.of(","), Token.NEWLINE))
          .parenthesized()
          // Because `separated` combined things, this works nicely
          .lineSeparated();

        return TokenTree.of(
          Token.of("| %1$s".formatted(typeName)),
          params);
    }

    public TokenTree generateDependantErrorDataTypeConstructor(final DependentSmithyModel dependentSmithyModel) {
        final String errorType = nameResolver.dafnyTypesModuleForNamespace(dependentSmithyModel.namespace()) + ".Error";
        final String errorConstructorName = errorType
          .replace("Types.Error", "");

        return TokenTree.of(
          Token.of("| %s(%s: %s)"
            .formatted(errorConstructorName, errorConstructorName, errorType))
        );
    }

    public TokenTree generateAbstractBody() {
        final String typesModuleName = DafnyNameResolver
          .dafnyTypesModuleForNamespace(serviceShape.getId().getNamespace());

        final TokenTree abstractModulePrelude = TokenTree
          .of(Stream
            .of(
              "import opened Wrappers",
              "import opened StandardLibrary.UInt",
              "import opened UTF8",
              "import opened Types = %s".formatted(typesModuleName)
            )
            .map(i -> Token.of(i)))
          .lineSeparated();

      if (serviceShape.hasTrait(ServiceTrait.class)) {
        return TokenTree
          .of(
            abstractModulePrelude,
            generateAbstractAwsServiceClass(serviceShape)
          )
          .lineSeparated();
      } else if (serviceShape.hasTrait(LocalServiceTrait.class)) {
          return TokenTree
            .of(
              abstractModulePrelude,
              generateAbstractLocalService(serviceShape)
            )
            .lineSeparated();
      } else {
        throw new IllegalStateException("Service does not have supported trait");
      }
    }

    public TokenTree generateAbstractLocalService(ServiceShape serviceShape)  {
        if (!serviceShape.hasTrait(LocalServiceTrait.class)) throw new IllegalStateException("MUST be an LocalService");
        final LocalServiceTrait localServiceTrait = serviceShape.expectTrait(LocalServiceTrait.class);

        final String configTypeName = localServiceTrait.getConfigId().getName();
        final String defaultFunctionMethodName = "Default%s".formatted(configTypeName);

        final TokenTree defaultConfig = TokenTree
          .of("function method %s(): %s".formatted(defaultFunctionMethodName, configTypeName));


        final TokenTree serviceMethod = TokenTree
          .of(
            "method %s(config: %s := %s())"
              .formatted(
                localServiceTrait.getSdkId(),
                configTypeName,
                defaultFunctionMethodName
              ),
            // Yes, Error is hard coded
            // this can work because we need to be able Errors from other modules...
            "returns (res: Result<%s, Error>)".formatted(nameResolver.traitForServiceClient(serviceShape)),
            "ensures res.Success? ==> fresh(res.value)"
            )
          .lineSeparated();

        return TokenTree
          .of(
            defaultConfig,
            serviceMethod
          )
          .lineSeparated();
    }

    public TokenTree generateAbstractAwsServiceClass(ServiceShape serviceShape) {
        if (!serviceShape.hasTrait(ServiceTrait.class)) throw new IllegalStateException("MUST be an AWS Service API");
        final ServiceTrait serviceTrait = serviceShape.expectTrait(ServiceTrait.class);
        final String sdkId = serviceTrait.getSdkId();

        final String configTypeName = "%sClientConfigType".formatted(sdkId);
        final TokenTree configType = TokenTree
          .of("datatype %s = %s".formatted(configTypeName, configTypeName)
        );
        final String defaultFunctionMethodName = "Default%s".formatted(configTypeName);

        final TokenTree defaultConfig = TokenTree
          .of("function method %s(): %s".formatted(defaultFunctionMethodName, configTypeName));

        final TokenTree factory = TokenTree
          .of(
            "method {:extern} %sClient()".formatted(serviceTrait.getSdkId()),
            "returns (res: Result<%s, Error>)".formatted(nameResolver.traitForServiceClient(serviceShape))
          ).lineSeparated();

        return TokenTree
          .of(
            configType,
            defaultConfig,
            factory
          )
          .lineSeparated();
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

    @VisibleForTesting
    public Model getModel() {
        return model;
    }
}
