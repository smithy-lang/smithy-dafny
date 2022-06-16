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
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.HashSet;
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

        final String typesModuleName = DafnyNameResolver
          .dafnyTypesModuleForNamespace(serviceShape.getId().getNamespace());
        final TokenTree typesModuleHeader = Token.of("module %s".formatted(typesModuleName));

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
            case SERVICE -> {
                if (shape != serviceShape) {
                    throw new IllegalStateException("Unexpected service shape found");
                }
                yield TokenTree
                  .of(generateServiceTraitDefinition())
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

    public TokenTree generateServiceTraitDefinition() {

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
              .map(this::generateOperationMethod))
          .lineSeparated();
        final TokenTree predicates = TokenTree
          .of(
            serviceShape
              .getAllOperations()
              .stream()
              .flatMap(operation ->
                Stream.of(
                  generatePredicateCalledWith(operation),
                  generatePredicateSucceededWith(operation)
                )
              )
          )
          .lineSeparated();

        return TokenTree
          .of(
            trait,
            methods.braced(),
            TokenTree.of("// Predicates are separated from the trait. This is temporary."),
            predicates
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
        // See generateOperationPredicatesAndMethod, when updated, change me back
        final TokenTree methods = TokenTree
          .of(
              resource
                .getAllOperations()
                .stream()
                .map(this::generateOperationMethod)
          )
          .lineSeparated();

        final TokenTree predicates = TokenTree
          .of(
            resource
              .getAllOperations()
              .stream()
              .flatMap(operation ->
                Stream.of(
                  generatePredicateCalledWith(operation),
                  generatePredicateSucceededWith(operation)
                )
              )
          )
          .lineSeparated();

        return TokenTree
          .of(
            trait,
            methods.braced(),
            TokenTree.of("// Predicates are separated from the trait. This is temporary."),
            predicates
          )
          .lineSeparated();
    }

    // TODO see: https://github.com/dafny-lang/dafny/issues/2150
    // So the predicates can't be in the trait until that is fixed
    public TokenTree generateOperationPredicatesAndMethod(final ShapeId operationShapeId) {

        final TokenTree calledWithPredicate = this.generatePredicateCalledWith(operationShapeId);
        final TokenTree succeededWithPredicate = this.generatePredicateSucceededWith(operationShapeId);
        final TokenTree method = this.generateOperationMethod(operationShapeId);

        return TokenTree
          .of(
            calledWithPredicate,
            succeededWithPredicate,
            method
          )
          .lineSeparated()
          .append(Token.NEWLINE);
    }

    public TokenTree generateOperationParams(final OperationShape operationShape) {
        return operationShape.getInput()
          .map(nameResolver::baseTypeForShape)
          .map(inputType -> TokenTree.of("input:", inputType))
          .orElse(TokenTree.empty());
    }


    private TokenTree generateOperationMethod(final ShapeId operationShapeId) {
        return generateOperationMethod(operationShapeId, TokenTree.empty());
    }

    private TokenTree generateOperationMethod(final ShapeId operationShapeId, final TokenTree attributeAnnotation) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);

        // If an operation is @readonly,
        // then it is treated as a Dafny function
        // TODO: This is only true for local services...
        final boolean isReadOnly = operationShape.hasTrait(ReadonlyTrait.class);

        final TokenTree name = TokenTree
          .of(isReadOnly ? "function method" : "method")
          .append(attributeAnnotation)
          .append(TokenTree.of(nameResolver.methodForOperation(operationShape)));
        final TokenTree operationParams = generateOperationParams(operationShape).parenthesized();
        final TokenTree returns = TokenTree
          .of("%s (output: %s)"
            .formatted(
              isReadOnly ? ":" : "returns",
              nameResolver.returnTypeForOperation(operationShape)
            ));

        // The formal Dafny name for this section of a method is "specification".
        // To avoid confusion with RFC-style "specifications", instead use the term "conditions".
        TokenTree conditions = TokenTree.empty();

        TokenTree ensureCalledWith = TokenTree.of(
                "ensures "
                        + nameResolver.predicateCalledWith(operationShape)
        );
        TokenTree ensureSucceededWith = TokenTree.of(
                "ensures output.Success? ==> "
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
        return TokenTree
          .of(
            name,
            operationParams,
            returns,
            conditions.lineSeparated()
          )
          .lineSeparated();
    }

    private TokenTree generatePredicateCalledWith(
      final ShapeId operationShapeId
    ) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);
        final TokenTree operationParams = generateOperationParams(operationShape);
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
      final ShapeId operationShapeId
    ) {
        final OperationShape operationShape = model.expectShape(operationShapeId, OperationShape.class);
        final TokenTree operationParams = generateOperationParams(operationShape);

        TokenTree params = TokenTree.empty();
        if (operationShape.getInput().isPresent()) {
            params = TokenTree.of(params, operationParams);
        }
        if (operationShape.getInput().isPresent() && operationShape.getOutput().isPresent()) {
            params = params.append(TokenTree.of(","));
        }
        if (operationShape.getOutput().isPresent()) {
            final String returnType = operationShape
              .getOutput()
              .map(nameResolver::baseTypeForShape)
              .get();

            params = params.append(TokenTree.of("output: %s".formatted(returnType)));
        }
        params = params.parenthesized();
        final TokenTree name = TokenTree.of("predicate {:opaque}", nameResolver.predicateSucceededWith(operationShape));
        final TokenTree body = TokenTree.of("{true}");
        return TokenTree.of(name, params, body);
    }


    /**
     * Generates the service's error types that are not modeled directly. These include:
     * <ul>
     *     <li>the error trait</li>
     *     <li>an "unknown error" class</li>
     * </ul>
     */
    public TokenTree generateModeledErrorDataType() {
    // TODO need to add dependent errors...
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
            "returns (res: Result<%s, Error>)".formatted(nameResolver.traitForServiceClient(serviceShape))
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

//        final TokenTree className = TokenTree
//          .of(
//            "class {:extern} ",
//            serviceTrait.getSdkId(),
//            "extends %s".formatted(nameResolver.traitForServiceClient(serviceShape))
//          );
//
//        final TokenTree constructor = TokenTree.of(
//            "constructor {:extern} (config: %s := %s())"
//              .formatted(configTypeName, defaultFunctionMethodName)
//        );
//
//        final TokenTree predicatesAndMethods = TokenTree
//          .of(
//            serviceShape
//              .getAllOperations()
//              .stream()
//              .map(operation -> this.generateOperationMethod(operation, TokenTree.of("{:extern}")))
//          )
//          .lineSeparated();

        return TokenTree
          .of(
            configType,
            defaultConfig,
            factory
//            className,
//            TokenTree
//              .of(
//                constructor,
//                predicatesAndMethods
//              )
//              .lineSeparated()
//              .braced()
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
