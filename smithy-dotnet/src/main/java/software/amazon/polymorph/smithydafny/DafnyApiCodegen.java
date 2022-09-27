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
                  .relativize(d.modelPath().resolve("../src/Index.dfy"))
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
              nameResolver.modulePreludeStandardImports(),
              nameResolver
                .dependentModels()
                .stream()
                .map(d ->
                  "import " + nameResolver.dafnyTypesModuleForNamespace(d.namespace())))
            .map(i -> Token.of(i))
          )
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
              // Error types are generated *after*
              // all other types to account
              // for any dependent modules
              generateModeledErrorDataType()
            )
            .lineSeparated()
            .braced();

        final Path path = Path.of("%s.dfy".formatted(typesModuleName));
        final TokenTree fullCode = TokenTree
          .of(
            includeDirectives,
            typesModuleHeader,
            typesModuleBody,
            generateAbstractServiceModule(serviceShape),
            generateAbstractOperationsModule(serviceShape)
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
        final TokenTree methods = TokenTree
          .of(
            serviceShape
              .getAllOperations()
              .stream()
              .flatMap(operation -> Stream.of(
                generateEnsuresPubliclyPredicate(serviceShape, operation),
                generateBodilessOperationMethodThatEnsuresCallEvents(serviceShape, operation, ImplementationType.CODEGEN),
                TokenTree.empty()
                )
              )
          )
          .lineSeparated();

        return TokenTree
          .of(
            generateHistoricalCallEventsForService(serviceShape),
            trait,
            methods
              .prepend(generateMutableInvariantInterface()
                .append(Token.of("ghost const %s: %s"
                  .formatted(
                    nameResolver.callHistoryFieldName(),
                    nameResolver.historicalCallHistoryClassForResource(serviceShape)))))
              .lineSeparated()
              .braced()
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
          // TODO: This is a hack to make the side effect happen
          // While there is no code to generate,
          // the module needs to be included
          // because we are obviously using it!
          final String sideEffect = nameResolver
            .dafnyModulePrefixForShapeId(model.expectShape(referenceTrait.getReferentId()));
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
            generateHistoricalCallEventsForResource(resource),
            trait,
            methods
              .prepend(generateMutableInvariantInterface()
                .append(Token.of("ghost const %s: %s"
                  .formatted(
                    nameResolver.callHistoryFieldName(),
                    nameResolver.historicalCallHistoryClassForResource(resource)))))
              .lineSeparated()
              .braced()
          )
          .lineSeparated();
    }


    public TokenTree generateHistoricalCallEventsForService(final ServiceShape service) {

        final TokenTree className = TokenTree
          .of("class %s"
            .formatted(nameResolver.historicalCallHistoryClassForResource(service))
          );
        final TokenTree constructor = TokenTree
          .of(
            service
              .getAllOperations()
              .stream()
              .map(operation -> model.expectShape(operation, OperationShape.class))
              .map(operation -> TokenTree.of(
                "%s := [];".formatted(nameResolver.historicalCallEventsForOperation(operation))
              ))
          )
          .lineSeparated()
          .braced()
          .prepend(Token.of("ghost constructor()"));
        final TokenTree fields = TokenTree
          .of(
            service
              .getAllOperations()
              .stream()
              .map(operation -> generateHistoricalCallEvents(operation))
          )
          .lineSeparated();

        return className
          .append(TokenTree
            .of(constructor, fields)
            .lineSeparated()
            .braced());
    }
    public TokenTree generateHistoricalCallEventsForResource(final ResourceShape resource) {

        final TokenTree className = TokenTree
          .of("class %s"
            .formatted(nameResolver.historicalCallHistoryClassForResource(resource))
          );
        final TokenTree constructor = TokenTree
          .of(
            resource
              .getAllOperations()
              .stream()
              .map(operation -> model.expectShape(operation, OperationShape.class))
              .map(operation -> TokenTree.of(
                "%s := [];".formatted(nameResolver.historicalCallEventsForOperation(operation))
                ))
          )
          .lineSeparated()
          .braced()
          .prepend(Token.of("ghost constructor()"));
        final TokenTree fields = TokenTree
          .of(
            resource
              .getAllOperations()
              .stream()
              .map(operation -> generateHistoricalCallEvents(operation))
          )
          .lineSeparated();

        return className
          .append(TokenTree
            .of(constructor, fields)
            .lineSeparated()
            .braced());
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

    private TokenTree generateMutableInvariantInterface() {
      return TokenTree
        .of(
          "// Helper to define any additional modifies/reads clauses",
          "// If your operations need to mutate state add it",
          "// in your constructor function:",
          "// %s := {your, fields, here, %s};".formatted(
            nameResolver.mutableStateFunctionName(),
            nameResolver.callHistoryFieldName()),
          "// If you do not need to mutate anything:",
          "// %s := {History};".formatted(
            nameResolver.mutableStateFunctionName(),
            nameResolver.callHistoryFieldName()
          ),
          "ghost const %s: set<object>".formatted(nameResolver.mutableStateFunctionName()),
          "// For an unassigned const field defined in a trait,",
          "// Dafny can only assign a value in the constructor.",
          "// This means that for Dafny to reason about this value,",
          "// it needs some way to know (an invariant),",
          "// about the state of the object.",
          "// This builds on the Valid/Repr paradigm",
          "// To make this kind requires is safe to add",
          "// to methods called from unverified code",
          "// the predicate MUST NOT take any arguments.",
          "// This means that the correctness of this requires",
          "// MUST only be evaluated by the class itself.",
          "// If you require any additional mutation,",
          "// Then you MUST ensure everything you need in %s.".formatted(nameResolver.validStateInvariantName()),
          "// You MUST also ensure %s in your constructor.".formatted(nameResolver.validStateInvariantName()),
          "predicate %s()".formatted(nameResolver.validStateInvariantName()),
          "ensures %s() ==> %s in %s"
            .formatted(
              nameResolver.validStateInvariantName(),
              nameResolver.callHistoryFieldName(),
              nameResolver.mutableStateFunctionName()
            )
        )
        .lineSeparated()
        .append(TokenTree.empty())
        .lineSeparated();
    }

    private TokenTree generateBodilessOperationMethodThatEnsuresCallEvents(
      final ServiceShape serviceShape,
      final ShapeId operationShapeId,
      final ImplementationType implementationType
    ) {
      final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);
      final Boolean isFunction = nameResolver.isFunction(serviceShape, operationShape);

      final TokenTree config = implementationType.equals(ImplementationType.ABSTRACT)
        ? TokenTree.of("config: %s, ".formatted(
          DafnyNameResolver.internalConfigType()))
        : TokenTree.empty();

      final TokenTree operationMethod = TokenTree
        .of(
          TokenTree
            .of(nameResolver.executableType(serviceShape, operationShape))
            .append(Token.of(nameResolver.publicMethodNameForOperation(operationShape)))
            .append(generateOperationParams(operationShape)
              .prepend(config)
              .dropEmpty()
              .parenthesized()),
          generateOperationReturnsClause(serviceShape, operationShape),
          isFunction
            ? TokenTree.of("// Functions that are transparent do not need ensures")
            : TokenTree
            .of(
              generateMutableInvariantForMethod(serviceShape, operationShapeId, implementationType),
              generateEnsuresForEnsuresPubliclyPredicate(operationShapeId),
              !implementationType.equals(ImplementationType.ABSTRACT)
                ? generateEnsuresHistoricalCallEvents(operationShapeId)
                : TokenTree.empty()
            )
            .dropEmpty()
            .lineSeparated()
        )
        .lineSeparated();
      return TokenTree
        .of(
          // This function returns the bodiless method
          // at the end of the TokenTree
          // so that other callers can compose
          // and add bodies.
          TokenTree.of(!implementationType.equals(ImplementationType.ABSTRACT)
            ? "// The public method to be called by library consumers"
            : "// The private method to be refined by the library developer"),
          operationMethod
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
            generateEnsuresPubliclyPredicate(serviceShape, operationShapeId),
            generateBodilessOperationMethodThatEnsuresCallEvents(serviceShape, operationShapeId, ImplementationType.CODEGEN),
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
                generateMutableInvariantForMethod(serviceShape, operationShapeId, ImplementationType.DEVELOPER),
                generateEnsuresForEnsuresPubliclyPredicate(operationShapeId),
                generateEnsuresUnchangedCallHistory(operationShapeId)
              )
              .lineSeparated()
          )
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

    /*
        The purpose of this ENUM is to distinguish who is writing the body of the method.
        In the case of a Resource we wrap the call history into the implemented method `MethodName`
        and leave a `MethodName'` for the developer to write.
        This means that there is a relationship between specification of these two methods
        but that this relationship is not exactly the same.
     */
    public enum ImplementationType {
        // TODO, this is too complicated, please simplify
        DEVELOPER, CODEGEN, ABSTRACT
    }

    private TokenTree generateMutableInvariantForMethod(
      final ServiceShape serviceShape,
      final ShapeId operationShapeId,
      final ImplementationType implementationType
    ) {

      final String historySeq = implementationType == ImplementationType.CODEGEN
          ? "%s`%s".formatted(nameResolver.callHistoryFieldName(), operationShapeId.getName())
          : "";

      final TokenTree requires = OperationMemberRequires(operationShapeId, implementationType);
      final TokenTree ensures = OperationMemberEnsures(operationShapeId, implementationType);
      final TokenTree modifiesSet = OperationModifiesInputs(operationShapeId, implementationType);

      final TokenTree modifies = TokenTree
        .of(
          modifiesSet,
          Token.of(historySeq)
        )
        .flatten()
        .dropEmpty()
        .separated(Token.of(",\n"))
        .prependToNonEmpty(Token.of("modifies"));
      final TokenTree decreases = modifiesSet
        .flatten()
        .dropEmpty()
        .separated(Token.of(",\n"))
        .prependToNonEmpty(TokenTree
          .of(
            "// Dafny will skip type parameters when generating a default decreases clause.",
            "decreases"
          )
          .lineSeparated()
        );

      return TokenTree
        .of(
          requires,
          modifies,
          decreases,
          ensures
        )
        .dropEmpty()
        .lineSeparated();
    }

    private TokenTree OperationMemberRequires(
      final ShapeId operationShapeId,
      final ImplementationType implementationType
    ) {
      final String validStateInvariantName = nameResolver.validStateInvariantName();
      final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);

      final TokenTree inputReferencesThatNeedValidState = operationShape
        .getInput()
        .map(shapeId -> TokenTree
          .of(ModelUtils
            .streamStructureMembers(model.expectShape(shapeId, StructureShape.class))
            // Input members with a ReferenceTrait will have a `ValidState` predicate
            // This invariant needs to be maintained across all method calls
            .filter(this::OnlyReferenceStructures)
            .map(member -> OperationMemberValidState(member, operationShape, InputOutput.INPUT, implementationType))
            .map(TokenTree::of)
          )
        )
        .orElse(TokenTree.empty());
      return Token.of(!implementationType.equals(ImplementationType.ABSTRACT)
          ? "\n && %s()".formatted(validStateInvariantName)
          : "\n && %s(config)".formatted(nameResolver.validConfigPredicate()))
        .append(inputReferencesThatNeedValidState)
        .dropEmpty()
        .prependToNonEmpty(Token.of("requires"));
    }

  private TokenTree OperationMemberEnsures(
    final ShapeId operationShapeId,
    final ImplementationType implementationType
  ) {
    final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);
    final String validStateInvariantName = nameResolver.validStateInvariantName();

    final TokenTree outputReferencesThatNeedValidState = operationShape
      .getOutput()
      .map(shapeId -> model.expectShape(shapeId, StructureShape.class))
      .map(structureShape -> ModelUtils
        .streamStructureMembers(structureShape)
        // Input members with a ReferenceTrait will have a `ValidState` predicate
        // This invariant needs to be maintained across all method calls
        .filter(this::OnlyReferenceStructures)
        .map(member -> OperationMemberValidState(member, operationShape, InputOutput.OUTPUT, implementationType))
      )
      .map(TokenTree::of)
      .map(memberTokens -> {
        if (memberTokens.isEmpty()) return memberTokens;
        return TokenTree
          .of(
            Token.of("output.Success? ==> "),
            memberTokens
          )
          .parenthesized()
          .prepend(Token.of("&&"));
      })
      .orElse(TokenTree.empty());

    return TokenTree
      .of(
        Token.of(!implementationType.equals(ImplementationType.ABSTRACT)
          ? "&& %s()".formatted(validStateInvariantName)
          : "&& %s(config)".formatted(nameResolver.validConfigPredicate())),
        outputReferencesThatNeedValidState
      )
      .dropEmpty()
      .lineSeparated()
      .prependToNonEmpty(Token.of("ensures"))
      .lineSeparated();
  }

    private Boolean OnlyReferenceStructures(MemberShape member) {
        final Shape target = model.expectShape(member.getTarget());

        return
          // If the member is a reference type
          (
            target.getType() == ShapeType.STRUCTURE)
            && target.hasTrait(ReferenceTrait.class)
          // If the member is a LIST of a reference type
          || (
            target.getType() == ShapeType.LIST
              && model
              .expectShape(
                  target
                    .asListShape()
                    .get()
                    .getMember()
                    .getTarget())
              .hasTrait(ReferenceTrait.class)
            );
    }

    public enum InputOutput {
      INPUT, OUTPUT
    }
    private TokenTree OperationMemberValidState(
      final MemberShape member,
      final OperationShape operationShape,
      final InputOutput direction,
      final ImplementationType implementationType
    ) {
      final String validStateInvariantName = nameResolver.validStateInvariantName();
      final boolean isOutput = direction == InputOutput.OUTPUT;

      final ShapeId directionShape = direction == InputOutput.INPUT
        // The member MUST be a member of input or output
        // so there MUST be such a shape.
        ? operationShape.getInput().get()
        : operationShape.getOutputShape();

      if (member.getId() == directionShape.withMember(member.getMemberName())) {
        throw new IllegalStateException("Member not on operation");
      }

      final boolean isList = model.expectShape(member.getTarget()).getType() == ShapeType.LIST;
      // This is tricky, given where we are, there MUST be an output shape.
      // If this output is @positional,
      // then we need to drop the member name
      final String memberName = model.expectShape(directionShape).hasTrait(PositionalTrait.class)
        ? ""
        : ".%s".formatted(member.getMemberName());

      final String varName = direction == InputOutput.INPUT
        ? "input" + memberName
        : "output.value" + memberName; // These all expect to be appended to "output.Success? ==> "

      // Inputs can not be fresh
      // so if they are added to our output
      // then we can not prove freshness of these items
      final TokenTree removeInputs = direction == InputOutput.OUTPUT
        ? OperationModifiesInputs(operationShape.getId(), implementationType)
            .prependSeperated(Token.of("-"))
        : TokenTree.empty();

      // We need to do 3 things here
      // first, we need the member to have ValidState
      // second, its Modifies set MUST NOT be shared.
      // This second claim is to ensure that state can be reasoned about
      // third, everything MUST be fresh. This will make using things _much_ simpler
      // you may hate me now, but you will come around
      if (member.isRequired() && !isList) {
        // Required single item
        return TokenTree
          .of(
            Token.of("%s.%s()".formatted(varName, validStateInvariantName)),
            Token.of(
              // If we are putting the method in an abstract module
              // then there is no object to share state with
              !implementationType.equals(ImplementationType.ABSTRACT)
              ? "%s.Modifies !! {%s}".formatted(varName, nameResolver.callHistoryFieldName())
              : ""),
            Token.of(isOutput ? "fresh(%s)".formatted(varName) : ""),
            isOutput
              ? Token
              .of("fresh")
              .append(TokenTree
                .of(Token.of("%s.Modifies".formatted(varName)), removeInputs)
                .parenthesized())
              : TokenTree.empty()
          )
          .dropEmpty()
          .prependSeperated(Token.of("\n &&"));
      } else if (!member.isRequired() && !isList) {
        // Optional single item
        return TokenTree
          .of(
            "&& ( %s.Some? ==>".formatted(varName),
            "&& %s.value.%s()".formatted(varName, validStateInvariantName),
            // If we are putting the method in an abstract module
            // then there is no object to share state with
            !implementationType.equals(ImplementationType.ABSTRACT)
            ? "&& %s.value.Modifies !! {%s}".formatted(varName, nameResolver.callHistoryFieldName())
            : "",
            isOutput ? "&& fresh(%s.value)".formatted(varName) : "",
            isOutput ? "&& fresh(%s.value.Modifies)".formatted(varName) : "",
            ")"
          )
          .dropEmpty()
          .lineSeparated();
      } else if (isList && member.isRequired()) {
        // Required list item
        return TokenTree
          .of(
            "&& ( forall i <- %s ::".formatted(varName),
            "&& i.%s()".formatted(validStateInvariantName),
            // If we are putting the method in an abstract module
            // then there is no object to share state with
            !implementationType.equals(ImplementationType.ABSTRACT)
            ? "&& i.Modifies !! {%s}".formatted(nameResolver.callHistoryFieldName())
            : "",
            isOutput ? "&& fresh(i)" : "",
            isOutput ? " && fresh(i.Modifies)" : "",
            ")"
          )
          .dropEmpty()
          .lineSeparated();
      } else if (isList && !member.isRequired()) {
        // Optional list item
        return TokenTree
          .of(
            "&& ( %s.Some? ==>".formatted(varName),
            "&& ( forall i <- %s.value ::".formatted(varName),
            "&& i.%s()".formatted(validStateInvariantName),
            // If we are putting the method in an abstract module
            // then there is no object to share state with
            !implementationType.equals(ImplementationType.ABSTRACT)
            ? "&& i.Modifies !! {%s}".formatted(nameResolver.callHistoryFieldName())
            : "",
            isOutput ? "&& fresh(i)" : "",
            isOutput ? " && fresh(i.Modifies)" : "",
            "))"
          )
          .dropEmpty()
          .lineSeparated();
      } else {
        throw new IllegalStateException("Unsupported shape type");
      }
    }

    private TokenTree OperationModifiesInputs(
      final ShapeId operationShapeId,
      final ImplementationType implementationType
    ){
      final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);
      return operationShape
        .getInput()
        .map(shapeId -> model.expectShape(shapeId, StructureShape.class))
        .map(structureShape -> ModelUtils
          .streamStructureMembers(structureShape)
          // Input members with a ReferenceTrait will have mutable state
          // This state needs to be maintained across all method calls
          .filter(this::OnlyReferenceStructures)
          .map(member -> OperationMemberModifies(member, operationShape))
        )
        .map(TokenTree::of)
        .orElse(TokenTree.empty())
        .prepend(
          // This lets us keep track of any additional modifications
          implementationType == ImplementationType.ABSTRACT
            // The abstract operations do not have a class with a `Modifies` property
            ? Token.of("%s(config)".formatted(nameResolver.modifiesInternalConfig()))
            // The class has a `Modifies` property
            : Token.of("%s"
                .formatted(nameResolver.mutableStateFunctionName()))
        )
        .flatten();
    }

    private TokenTree OperationMemberModifies(
      final MemberShape member,
      final OperationShape operationShape
    ) {
      final ShapeId directionShape = operationShape.getInput().get();

      if (member.getId() == directionShape.withMember(member.getMemberName())) {
        throw new IllegalStateException("Member not on operation");
      }

      final boolean isList = model.expectShape(member.getTarget()).getType() == ShapeType.LIST;
      // This is tricky, given where we are, there MUST be an output shape.
      // If this output is @positional,
      // then we need to drop the member name
      final String memberName = model.expectShape(directionShape).hasTrait(PositionalTrait.class)
        ? ""
        : ".%s".formatted(member.getMemberName());

      final String varName = "input" + memberName;

      // If we have a reference input,
      // then we MAY modify that input.
      // This means we will need both
      // a modifies and a decreases' clause.
      // The decreases clause is because
      // Dafny will skip type parameters
      // when generating a default decreases clause.
      if (member.isRequired() && !isList) {
        // Required single item
        return TokenTree
          .of(
            "%s.Modifies".formatted(varName)
          );
      } else if (!member.isRequired() && !isList) {
        // Optional single item
        return TokenTree
          .of(
            "(if %s.Some? then %s.value.Modifies else {})"
              .formatted(varName, varName)
          )
          .lineSeparated();
      } else if (isList && member.isRequired()) {
        // Required list item
        return TokenTree
          .of(
            "(set m: object, i | i in %s && m in i.Modifies :: m)"
              .formatted(varName)
          )
          .lineSeparated();
      } else if (isList && !member.isRequired()) {
        // Optional list item
        return TokenTree
          .of(
            "(if %s.Some? then (set m: object, i | i in %s.value && m in i.Modifies :: m) else {})"
              .formatted(varName, varName)
          )
          .lineSeparated();
      } else {
        throw new IllegalStateException("Unsupported shape type");
      }
    }


    private TokenTree generateEnsuresHistoricalCallEvents(
        final ShapeId operationShapeId
    ) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);

        final String historicalCallEventsForOperation = "%s.%s"
          .formatted(
            nameResolver.callHistoryFieldName(),
            nameResolver.historicalCallEventsForOperation(operationShape));

        return TokenTree
          .of(
            Token.of("ensures"),
            Token.of("%s == old(%s) + [%s(input, output)]"
              .formatted(
                historicalCallEventsForOperation,
                historicalCallEventsForOperation,
                nameResolver.callEventTypeName())
            )
          );
    }

    private TokenTree generateAccumulateHistoricalCallEvents(
      final ShapeId operationShapeId
    ) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);
        final String historicalCallEvents = "%s.%s"
          .formatted(
            nameResolver.callHistoryFieldName(),
            nameResolver.historicalCallEventsForOperation(operationShape));
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
      final ServiceShape serviceShape,
      final ShapeId operationShapeId
    ) {
      final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);
      final Boolean isFunction = nameResolver.isFunction(serviceShape, operationShape);

      return isFunction
        ? TokenTree
        .of("// Functions are deterministic, no need for historical call events or ensures indirection")
        : TokenTree
        .of(
          TokenTree
            .of(
              "predicate %s(%s, %s)"
                .formatted(
                  nameResolver.ensuresPubliclyPredicate(operationShape),
                  generateOperationParams(operationShape),
                  generateOperationOutputParams(operationShape)
                )
            )
        )
        .lineSeparated();

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

    private TokenTree generateEnsuresUnchangedCallHistory(
      final ShapeId operationShapeId
    ) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);

        return TokenTree
          .of(
            "ensures unchanged(%s)".formatted(nameResolver.callHistoryFieldName())
          );
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
        final TokenTree abstractModulePrelude = TokenTree
          .of(DafnyNameResolver.abstractModulePrelude(serviceShape))
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
              abstractModulePrelude, generateAbstractLocalService(serviceShape)
            )
            .lineSeparated();
      } else {
        throw new IllegalStateException("Service does not have supported trait");
      }
    }

    public TokenTree generateAbstractServiceModule(ServiceShape serviceShape) {
      final String moduleNamespace = DafnyNameResolver
        .dafnyNamespace(serviceShape.getId().getNamespace())
        .replace(".", "");
      final TokenTree abstractModulePrelude = TokenTree
        .of(DafnyNameResolver.abstractModulePrelude(serviceShape))
        .lineSeparated();
      final TokenTree moduleHeader = TokenTree.of("abstract module Abstract%sService".formatted(moduleNamespace));

      if (serviceShape.hasTrait(ServiceTrait.class)) {
        return moduleHeader
          .append(Token
            .of(
              abstractModulePrelude,
              generateAbstractAwsServiceClass(serviceShape)
            )
            .lineSeparated()
            .braced()
          );
      } else if (serviceShape.hasTrait(LocalServiceTrait.class)) {
        final TokenTree operationsPrelude = TokenTree
          .of(
            "import Operations : Abstract%sOperations".formatted(moduleNamespace)
          )
          .lineSeparated();

        final TokenTree methods = TokenTree
          .of(
            serviceShape
              .getAllOperations()
              .stream()
              .flatMap(operation -> Stream.of(
                nameResolver.isFunction(serviceShape, model.expectShape(operation, OperationShape.class))
                  ? Token.empty()
                  : TokenTree
                  .of(
                    generateEnsuresPubliclyPredicate(serviceShape, operation),
                    TokenTree
                      .of(
                        "{Operations.%s(input, output)}"
                          .formatted(
                            nameResolver.ensuresPubliclyPredicate(model.expectShape(operation, OperationShape.class))
                          )
                      )
                  )
                  .lineSeparated(),
                generateBodilessOperationMethodThatEnsuresCallEvents(serviceShape, operation, ImplementationType.CODEGEN),
                TokenTree
                  .of(
                    nameResolver.isFunction(serviceShape, model.expectShape(operation, OperationShape.class))
                    ? TokenTree.of("Operations.%s(config, input)".formatted(
                      operation.getName()
                    ))
                    : TokenTree.of(
                      Token.of("output := Operations.%s(config, input);"
                        .formatted(
                          operation.getName()
                        )),
                        generateAccumulateHistoricalCallEvents(operation)
                    )
                      .lineSeparated()
                  )
                  .lineSeparated()
                  .braced(),
                  TokenTree.empty()
                )
              )
          )
          .lineSeparated();

        final String clientName = serviceShape.expectTrait(LocalServiceTrait.class).getSdkId();
        final String internalConfig = DafnyNameResolver.internalConfigType();

        final TokenTree body =  TokenTree
          .of(
            abstractModulePrelude,
            operationsPrelude,
            generateAbstractLocalService(serviceShape),
            TokenTree.of("class %sClient extends %s"
              .formatted(clientName, nameResolver.traitForServiceClient(serviceShape))),
            TokenTree.of(
              TokenTree.of("constructor(config: Operations.%s)".formatted(internalConfig)),
              TokenTree.of("requires Operations.%s(config)"
                .formatted(nameResolver.validConfigPredicate())),
              TokenTree.of("ensures"),
              TokenTree.of("&& %s()".formatted(nameResolver.validStateInvariantName())),
              TokenTree.of("&& fresh(%s)".formatted(nameResolver.callHistoryFieldName())),
              TokenTree.of("&& this.config == config"),
              TokenTree.of("const config: Operations.%s".formatted(internalConfig)),
              TokenTree.of("predicate %s()".formatted(nameResolver.validStateInvariantName())),
              TokenTree.of("ensures %s() ==>".formatted(nameResolver.validStateInvariantName())),
              TokenTree.of("&& Operations.%s(config)".formatted(nameResolver.validConfigPredicate())),
              TokenTree.of("&& %s !in Operations.%s(config)"
                .formatted(nameResolver.callHistoryFieldName(), nameResolver.modifiesInternalConfig())),
              TokenTree.of("&& %s == Operations.%s(config) + {%s}"
                .formatted(
                  nameResolver.mutableStateFunctionName(),
                  nameResolver.modifiesInternalConfig(),
                  nameResolver.callHistoryFieldName())),
              methods
            ).lineSeparated().braced()
          )
          .lineSeparated()
          .braced();


        return TokenTree
          .of(
            Token.of("abstract module Abstract%sService".formatted(moduleNamespace)),
            body
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
            "returns (res: Result<%sClient, Error>)"
              .formatted(localServiceTrait.getSdkId()),
            "ensures res.Success? ==> ",
            "&& fresh(res.value)",
            "&& fresh(res.value.%s)".formatted(nameResolver.mutableStateFunctionName()),
            "&& fresh(res.value.%s)".formatted(nameResolver.callHistoryFieldName()),
            "&& res.value.%s()".formatted(nameResolver.validStateInvariantName())
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
            "returns (res: Result<%s, Error>)".formatted(nameResolver.traitForServiceClient(serviceShape)),
            "ensures res.Success? ==> ",
            "&& fresh(res.value)",
            "&& fresh(res.value.%s)".formatted(nameResolver.mutableStateFunctionName()),
            "&& fresh(res.value.%s)".formatted(nameResolver.callHistoryFieldName()),
            "&& res.value.%s()".formatted(nameResolver.validStateInvariantName())
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
    private TokenTree generateAbstractOperationsModule(final ServiceShape serviceShape)
    {

      final String moduleNamespace = DafnyNameResolver
        .dafnyNamespace(serviceShape.getId().getNamespace())
        .replace(".", "");
      final TokenTree header = TokenTree.of("abstract module Abstract%sOperations"
        .formatted(moduleNamespace)
      );


      final String internalConfigType = DafnyNameResolver.internalConfigType();

      final TokenTree body = TokenTree
        .of(
          TokenTree.of(DafnyNameResolver.abstractModulePrelude(serviceShape)),
          TokenTree.of("type %s".formatted(internalConfigType)),
          TokenTree.of("predicate %s(config: %s)"
            .formatted(DafnyNameResolver.validConfigPredicate(), internalConfigType)),
          TokenTree.of("function %s(config: %s): set<object>"
            .formatted(DafnyNameResolver.modifiesInternalConfig(), internalConfigType)),
          TokenTree.of(
              serviceShape
                .getAllOperations()
                .stream()
                .map(operation -> TokenTree
                    .of(
                      generateEnsuresPubliclyPredicate(serviceShape, operation),
                      generateBodilessOperationMethodThatEnsuresCallEvents(
                        serviceShape,
                        operation,
                        ImplementationType.ABSTRACT
                      )
                    )
                    .flatten()
                    .lineSeparated()
                )
            )
            .lineSeparated()
        )
        .flatten()
        .lineSeparated()
        .braced();

      return TokenTree.of(header, body);
    }

    private TokenTree generateAbstractOperation(
      final ServiceShape serviceShape,
      final ShapeId operationShapeId
    ) {
      return TokenTree
        .of(
          generateEnsuresPubliclyPredicate(serviceShape, operationShapeId),
          generateBodilessOperationMethodThatEnsuresCallEvents(
            serviceShape,
            operationShapeId,
            ImplementationType.ABSTRACT
          )
        )
        .flatten()
        .lineSeparated();
    }
}
