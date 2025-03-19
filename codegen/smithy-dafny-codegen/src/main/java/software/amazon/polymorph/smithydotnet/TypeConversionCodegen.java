// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import static software.amazon.polymorph.smithydotnet.DotNetNameResolver.TYPE_CONVERSION_CLASS_NAME;
import static software.amazon.polymorph.smithydotnet.DotNetNameResolver.typeConverterForShape;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.FROM_DAFNY;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.TO_DAFNY;

import com.google.common.annotations.VisibleForTesting;
import java.nio.file.Path;
import java.util.*;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import javax.annotation.Nonnull;
import software.amazon.polymorph.smithydafny.DafnyNameResolver;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.traits.ExtendableTrait;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
import software.amazon.polymorph.utils.DafnyNameResolverHelpers;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.Token;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.*;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.synthetic.SyntheticEnumTrait;
import software.amazon.smithy.utils.StringUtils;

/**
 * Generates a {@code TypeConversion} class that includes all {@link TypeConverter}s needed for the operations in the
 * provided {@link Model}.
 */
public class TypeConversionCodegen {

  public static final String C_SHARP_SYSTEM_EXCEPTION = "System.Exception";
  // Edge case for constructors of Exceptions that extend the base Exception class.
  public static final List<String> ERROR_CTOR = Arrays.asList(
    "AwsCryptographicMaterialProvidersException",
    "EntryAlreadyExists",
    "EntryDoesNotExist",
    "InvalidAlgorithmSuiteInfo",
    "InvalidAlgorithmSuiteInfoOnDecrypt",
    "InvalidAlgorithmSuiteInfoOnEncrypt",
    "InvalidDecryptionMaterials",
    "InvalidDecryptionMaterialsTransition",
    "InvalidEncryptionMaterials",
    "InvalidEncryptionMaterialsTransition",
    "KeyStoreException",
    "KeyVectorException"
  );

  /**
   * A pair of type converter methods that converts between the compiled Dafny representation and the idiomatic C#
   * representation of a given {@link software.amazon.smithy.model.shapes.Shape} value.
   */
  public static record TypeConverter(
    ShapeId shapeId,
    TokenTree fromDafny,
    TokenTree toDafny
  ) {}

  public static final Path TYPE_CONVERSION_CLASS_PATH = Path.of(
    TYPE_CONVERSION_CLASS_NAME + ".cs"
  );

  protected final Model model;
  protected final ServiceShape serviceShape;
  protected final DotNetNameResolver nameResolver;

  public TypeConversionCodegen(
    final Model model,
    final ServiceShape serviceShape
  ) {
    this(model, serviceShape, new DotNetNameResolver(model, serviceShape));
  }

  public TypeConversionCodegen(
    final Model model,
    final ServiceShape serviceShape,
    final DotNetNameResolver nameResolver
  ) {
    this.model = model;
    this.serviceShape = serviceShape;
    this.nameResolver = nameResolver;
  }

  public Map<Path, TokenTree> generate() {
    final TokenTree prelude = TokenTree.of(
      // needed for LINQ operators like Select
      // system needed for creating an exception
      "using System.Linq;",
      "using System;"
    );
    final Stream<TypeConverter> modeledConverters = findShapeIdsToConvert()
      .stream()
      .map(model::expectShape)
      .map(this::generateConverter);
    final Stream<TypeConverter> unmodeledConverters =
      generateUnmodeledConverters();
    final Stream<TypeConverter> converters = Stream.concat(
      modeledConverters,
      unmodeledConverters
    );
    final TokenTree conversionClassBody = TokenTree
      .of(
        converters.flatMap(typeConverter ->
          Stream.of(typeConverter.fromDafny, typeConverter.toDafny)
        )
      )
      .prepend(conversionConstants())
      .lineSeparated()
      .braced();
    final TokenTree conversionClass = conversionClassBody
      .prepend(TokenTree.of("public static class", TYPE_CONVERSION_CLASS_NAME))
      .namespaced(Token.of(getTypeConversionNamespace()));
    return Map.of(TYPE_CONVERSION_CLASS_PATH, conversionClass.prepend(prelude));
  }

  private static TokenTree conversionConstants() {
    return TokenTree.of(
      """
      private const string ISO8601DateFormat = "yyyy-MM-dd\\\\THH:mm:ss.fff\\\\Z";

      private const string ISO8601DateFormatNoMS = "yyyy-MM-dd\\\\THH:mm:ss\\\\Z";
      """
    );
  }

  /**
   * Returns a stream of type converters for synthetic types (types that aren't defined in the model).
   */
  protected Stream<TypeConverter> generateUnmodeledConverters() {
    return Stream.of(generateCommonExceptionConverter());
  }

  /**
   * Returns all shape IDs that require converters.
   */
  @VisibleForTesting
  public Set<ShapeId> findShapeIdsToConvert() {
    Set<ShapeId> initialShapes = findInitialShapeIdsToConvert();
    return ModelUtils.findAllDependentShapes(initialShapes, model);
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
    final Set<ServiceShape> serviceShapes = model
      .getServiceShapes()
      .stream()
      .filter(serviceShape -> isInServiceNamespace(serviceShape.getId()))
      .collect(Collectors.toSet());

    // Collect resources defined in model...
    final Stream<ResourceShape> topLevelResourceShapes = model
      .getResourceShapes()
      .stream()
      .filter(resourceShape -> isInServiceNamespace(resourceShape.getId()));
    // ... and resources of collected services.
    final Stream<ResourceShape> serviceResourceShapes = serviceShapes
      .stream()
      .flatMap(serviceShape -> serviceShape.getResources().stream())
      .map(resourceShapeId ->
        model.expectShape(resourceShapeId, ResourceShape.class)
      );
    final Set<ResourceShape> resourceShapes = Stream
      .concat(topLevelResourceShapes, serviceResourceShapes)
      .collect(Collectors.toSet());

    // Collect operations defined in model...
    final Stream<OperationShape> topLevelOperationShapes = model
      .getOperationShapes()
      .stream()
      .filter(operationShape -> isInServiceNamespace(operationShape.getId()));
    // ... and operations of collected services...
    final Stream<OperationShape> serviceOperationShapes = serviceShapes
      .stream()
      .flatMap(serviceShape -> serviceShape.getAllOperations().stream())
      .map(operationShapeId ->
        model.expectShape(operationShapeId, OperationShape.class)
      );
    // ... and operations of collected resources.
    final Stream<OperationShape> resourceOperationShapes = resourceShapes
      .stream()
      .flatMap(resourceShape -> resourceShape.getAllOperations().stream())
      .map(operationShapeId ->
        model.expectShape(operationShapeId, OperationShape.class)
      );
    final Set<OperationShape> operationShapes = Stream
      .of(
        topLevelOperationShapes,
        serviceOperationShapes,
        resourceOperationShapes
      )
      .flatMap(Function.identity())
      .collect(Collectors.toSet());
    // Collect inputs/output structures for collected operations
    final Set<ShapeId> operationStructures = operationShapes
      .stream()
      .flatMap(operationShape ->
        Stream
          .of(operationShape.getInput(), operationShape.getOutput())
          .flatMap(Optional::stream)
      )
      .collect(Collectors.toSet());
    // Collect service client config structures
    final Set<ShapeId> clientConfigStructures = serviceShapes
      .stream()
      .map(serviceShape -> serviceShape.getTrait(LocalServiceTrait.class))
      .flatMap(Optional::stream)
      .map(LocalServiceTrait::getConfigId)
      .collect(Collectors.toSet());

    // Collect union shapes
    final Set<ShapeId> unionShapes = model
      .getUnionShapes()
      .stream()
      .filter(unionShape -> isInServiceNamespace(unionShape.getId()))
      .map(unionShape -> unionShape.getId())
      .collect(Collectors.toSet());

    // TODO add smithy v2 Enums
    // Collect enum shapes
    final Set<ShapeId> enumShapes = model
      .getShapesWithTrait(EnumTrait.class)
      .stream()
      .map(Shape::getId)
      .filter(this::isInServiceNamespace)
      .collect(Collectors.toSet());

    // Collect all specific error structures
    final Set<ShapeId> errorStructures = ModelUtils
      .streamServiceErrors(model, serviceShape)
      .map(Shape::getId)
      .collect(Collectors.toSet());

    // Collect into TreeSet so that we generate code in a deterministic order (lexicographic, in particular)
    final TreeSet<ShapeId> orderedSet = new TreeSet<ShapeId>();
    orderedSet.addAll(operationStructures);
    orderedSet.addAll(clientConfigStructures);
    orderedSet.addAll(unionShapes);
    orderedSet.addAll(errorStructures);
    orderedSet.addAll(enumShapes);
    return orderedSet;
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
      case ENUM -> generateEnumConverter(shape.asEnumShape().get());
      case INTEGER -> generateIntegerConverter(shape.asIntegerShape().get());
      case LONG -> generateLongConverter(shape.asLongShape().get());
      case DOUBLE -> generateDoubleConverter(shape.asDoubleShape().get());
      case TIMESTAMP -> generateTimestampConverter(
        shape.asTimestampShape().get()
      );
      case LIST -> generateListConverter(shape.asListShape().get());
      case MAP -> generateMapConverter(shape.asMapShape().get());
      case STRUCTURE -> generateStructureConverter(
        shape.asStructureShape().get()
      );
      case MEMBER -> generateMemberConverter(shape.asMemberShape().get());
      case UNION -> generateUnionConverter(shape.asUnionShape().get());
      default -> throw new IllegalStateException(
        "Shape %s not supported for generateConverter".formatted(shape)
      );
    };
  }

  public TypeConverter generateBlobConverter(final BlobShape blobShape) {
    final TokenTree fromDafnyBody = Token.of(
      "return new System.IO.MemoryStream(value.Elements);"
    );
    // enforce that MemoryStreams are backed by an array
    final TokenTree toDafnyBody = Token.of(
      """
      if (value.ToArray().Length == 0 && value.Length > 0)
      {
          throw new System.ArgumentException("Fatal Error: MemoryStream instance not backed by an array!");
      }
      return Dafny.Sequence<byte>.FromArray(value.ToArray());
      """
    );
    return buildConverterFromMethodBodies(
      blobShape,
      fromDafnyBody,
      toDafnyBody
    );
  }

  public TypeConverter generateBooleanConverter(
    final BooleanShape booleanShape
  ) {
    final TokenTree fromDafnyBody = Token.of("return value;");
    final TokenTree toDafnyBody = Token.of("return value;");
    return buildConverterFromMethodBodies(
      booleanShape,
      fromDafnyBody,
      toDafnyBody
    );
  }

  public TypeConverter generateStringConverter(final StringShape stringShape) {
    if (stringShape.hasTrait(EnumTrait.class)) {
      return generateEnumConverter(
        stringShape,
        stringShape.expectTrait(EnumTrait.class)
      );
    }

    if (stringShape.hasTrait(DafnyUtf8BytesTrait.class)) {
      return generateUtf8BytesConverter(stringShape);
    }

    final TokenTree fromDafnyBody = Token.of(
      "return new string(value.Elements);"
    );
    final TokenTree toDafnyBody = Token.of(
      "return Dafny.Sequence<char>.FromString(value);"
    );
    return buildConverterFromMethodBodies(
      stringShape,
      fromDafnyBody,
      toDafnyBody
    );
  }

  public TypeConverter generateIntegerConverter(
    final IntegerShape integerShape
  ) {
    final TokenTree fromDafnyBody = Token.of("return value;");
    final TokenTree toDafnyBody = Token.of("return value;");
    return buildConverterFromMethodBodies(
      integerShape,
      fromDafnyBody,
      toDafnyBody
    );
  }

  public TypeConverter generateLongConverter(final LongShape longShape) {
    final TokenTree fromDafnyBody = Token.of("return value;");
    final TokenTree toDafnyBody = Token.of("return value;");
    return buildConverterFromMethodBodies(
      longShape,
      fromDafnyBody,
      toDafnyBody
    );
  }

  public TypeConverter generateDoubleConverter(final DoubleShape doubleShape) {
    // BitConverter docs : https://learn.microsoft.com/en-us/dotnet/api/system.bitconverter?view=netstandard-2.1
    final TokenTree fromDafnyBody = Token.of(
      "return BitConverter.ToDouble(value.CloneAsArray(), 0);"
    );
    final TokenTree toDafnyBody = Token.of(
      "return Dafny.Sequence<byte>.FromArray(BitConverter.GetBytes(value));"
    );
    return buildConverterFromMethodBodies(
      doubleShape,
      fromDafnyBody,
      toDafnyBody
    );
  }

  public TypeConverter generateTimestampConverter(
    final TimestampShape timestampShape
  ) {
    final TokenTree fromDafnyBody = Token.of(
      """
      string timestampString = new string(value.Elements);
      return System.DateTime.ParseExact(timestampString, new[] {ISO8601DateFormat, ISO8601DateFormatNoMS}, System.Globalization.CultureInfo.InvariantCulture);
      """
    );
    final TokenTree toDafnyBody = Token.of(
      """
      string timestampString = value.ToString(ISO8601DateFormat, System.Globalization.CultureInfo.InvariantCulture);
      return Dafny.Sequence<char>.FromString(timestampString);
      """
    );
    return buildConverterFromMethodBodies(
      timestampShape,
      fromDafnyBody,
      toDafnyBody
    );
  }

  protected boolean enumListAndMapMembersAreStringsInCSharp() {
    return false;
  }

  public TypeConverter generateListConverter(final ListShape listShape) {
    final String listCSharpType = nameResolver.baseTypeForList(listShape);

    final MemberShape memberShape = listShape.getMember();
    final String memberDafnyType = nameResolver.dafnyTypeForShape(
      memberShape.getId()
    );
    final String memberCSharpType = nameResolver.baseTypeForMember(memberShape);
    final String memberToDafnyConverterName = typeConverterForShape(
      memberShape.getId(),
      TO_DAFNY
    );

    final String memberFromDafnyConverterName = typeConverterForShape(
      memberShape.getId(),
      FROM_DAFNY
    );
    final boolean convertMemberEnumToString =
      enumListAndMapMembersAreStringsInCSharp() &&
      model.expectShape(memberShape.getTarget()).hasTrait(EnumTrait.class);

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
          fromDafnyEnumConversion
        )
    );

    final TokenTree toDafnyBody = Token.of(
      "return Dafny.Sequence<%s>.FromArray(value%s.Select(%s).ToArray());".formatted(
          memberDafnyType,
          toDafnyEnumConversion,
          memberToDafnyConverterName
        )
    );

    return buildConverterFromMethodBodies(
      listShape,
      fromDafnyBody,
      toDafnyBody
    );
  }

  public TypeConverter generateMapConverter(final MapShape mapShape) {
    final MemberShape keyShape = mapShape.getKey();
    final MemberShape valueShape = mapShape.getValue();
    final String keyDafnyType = nameResolver.dafnyTypeForShape(
      keyShape.getId()
    );
    final String valueDafnyType = nameResolver.dafnyTypeForShape(
      valueShape.getId()
    );

    final String keyToDafnyConverterName = typeConverterForShape(
      keyShape.getId(),
      TO_DAFNY
    );
    final String keyFromDafnyConverterName = typeConverterForShape(
      keyShape.getId(),
      FROM_DAFNY
    );
    final String valueToDafnyConverterName = typeConverterForShape(
      valueShape.getId(),
      TO_DAFNY
    );
    final String valueFromDafnyConverterName = typeConverterForShape(
      valueShape.getId(),
      FROM_DAFNY
    );

    final boolean convertKeyEnumToString =
      enumListAndMapMembersAreStringsInCSharp() &&
      model.expectShape(keyShape.getTarget()).hasTrait(EnumTrait.class);
    final String fromDafnyKeyEnumConversion = convertKeyEnumToString
      ? ".Value"
      : "";

    final boolean convertValueEnumToString =
      enumListAndMapMembersAreStringsInCSharp() &&
      model.expectShape(valueShape.getTarget()).hasTrait(EnumTrait.class);
    final String fromDafnyValueEnumConversion = convertValueEnumToString
      ? ".Value"
      : "";

    final TokenTree fromDafnyBody = Token.of(
      "return value.ItemEnumerable.ToDictionary(pair => %s(pair.Car)%s, pair => %s(pair.Cdr)%s);".formatted(
          keyFromDafnyConverterName,
          fromDafnyKeyEnumConversion,
          valueFromDafnyConverterName,
          fromDafnyValueEnumConversion
        )
    );

    final String dafnyMapTypeArgs =
      "<%s, %s>".formatted(keyDafnyType, valueDafnyType);
    final TokenTree toDafnyBody = Token.of(
      """
      return Dafny.Map%s.FromCollection(value.Select(pair =>
          new Dafny.Pair%s(%s(pair.Key), %s(pair.Value))
      ));""".formatted(
          dafnyMapTypeArgs,
          dafnyMapTypeArgs,
          keyToDafnyConverterName,
          valueToDafnyConverterName
        )
    );
    return buildConverterFromMethodBodies(mapShape, fromDafnyBody, toDafnyBody);
  }

  public TypeConverter generateStructureConverter(
    final StructureShape structureShape
  ) {
    final Optional<ReferenceTrait> referenceTraitOptional =
      structureShape.getTrait(ReferenceTrait.class);
    if (referenceTraitOptional.isPresent()) {
      return generateReferenceStructureConverter(
        structureShape,
        referenceTraitOptional.get()
      );
    }

    final Optional<PositionalTrait> positionalTraitOptional =
      structureShape.getTrait(PositionalTrait.class);
    if (positionalTraitOptional.isPresent()) {
      return generatePositionalStructureConverter(structureShape);
    }

    if (structureShape.hasTrait(ErrorTrait.class)) {
      return generateSpecificModeledErrorConverter(structureShape);
    }

    return generateRegularStructureConverter(structureShape);
  }

  /**
   * This should not be called directly, instead call
   * {@link TypeConversionCodegen#generateStructureConverter(StructureShape)}.
   */
  private TypeConverter generateRegularStructureConverter(
    final StructureShape structureShape
  ) {
    final TokenTree concreteVar = Token.of(
      "%1$s concrete = (%1$s)value;".formatted(
          nameResolver.dafnyConcreteTypeForRegularStructure(structureShape)
        )
    );
    final TokenTree assignments = TokenTree
      .of(
        ModelUtils
          .streamStructureMembers(structureShape)
          .map(memberShape -> {
            final String dafnyMemberName = DotNetNameResolver.memberName(
              memberShape
            );
            final String propertyName =
              nameResolver.classPropertyForStructureMember(memberShape);
            final String propertyType;
            if (
              StringUtils.equals(
                nameResolver.classPropertyTypeForStructureMember(memberShape),
                AwsSdkDotNetNameResolver.DDB_ATTRIBUTE_VALUE_MODEL_NAMESPACE
              )
            ) {
              propertyType = AwsSdkDotNetNameResolver.DDB_V2_ATTRIBUTE_VALUE;
            } else {
              propertyType =
                nameResolver.classPropertyTypeForStructureMember(memberShape);
            }
            final String memberFromDafnyConverterName = typeConverterForShape(
              memberShape.getId(),
              FROM_DAFNY
            );

            final TokenTree checkIfPresent;
            if (nameResolver.memberShapeIsOptional(memberShape)) {
              checkIfPresent =
                Token.of("if (concrete.%s.is_Some)".formatted(dafnyMemberName));
            } else {
              checkIfPresent = TokenTree.empty();
            }
            // SizeEstimateRangeGb requires a list of double instead of the generated int list
            final TokenTree assign;
            if (StringUtils.equals(dafnyMemberName, "_SizeEstimateRangeGB")) {
              assign =
                Token.of(
                  "converted.%s = %s(concrete.%s).Select(i => (double) i).ToList();".formatted(
                      propertyName,
                      memberFromDafnyConverterName,
                      dafnyMemberName
                    )
                );
            } else {
              assign =
                Token.of(
                  "converted.%s = (%s) %s(concrete.%s);".formatted(
                      propertyName,
                      propertyType,
                      memberFromDafnyConverterName,
                      dafnyMemberName
                    )
                );
            }
            return TokenTree.of(checkIfPresent, assign);
          })
      )
      .lineSeparated();
    final String structureType = nameResolver.baseTypeForShape(
      structureShape.getId()
    );
    final TokenTree fromDafnyBody = TokenTree.of(
      concreteVar,
      Token.of("%1$s converted = new %1$s();".formatted(structureType)),
      assignments,
      Token.of("return converted;")
    );

    final TokenTree isSetTernaries = TokenTree
      .of(
        ModelUtils
          .streamStructureMembers(structureShape)
          .filter(nameResolver::memberShapeIsOptional)
          .map(this::generateExtractOptionalMember)
      )
      .lineSeparated();

    final TokenTree constructorArgs = TokenTree
      .of(
        ModelUtils
          .streamStructureMembers(structureShape)
          .map(this::generateConstructorArg)
          .map(Token::of)
      )
      .separated(Token.of(','));
    final TokenTree constructor = TokenTree.of(
      TokenTree.of("return new"),
      TokenTree.of(
        nameResolver.dafnyConcreteTypeForRegularStructure(structureShape)
      ),
      constructorArgs.parenthesized(),
      Token.of(';')
    );
    String validate = "value.Validate();";
    if (AwsSdkNameResolverHelpers.isInAwsSdkNamespace(structureShape.getId())) {
      validate = "";
    }
    final TokenTree toDafnyBody = TokenTree
      .of(TokenTree.of(validate), isSetTernaries, constructor)
      .lineSeparated();

    return buildConverterFromMethodBodies(
      structureShape,
      fromDafnyBody,
      toDafnyBody
    );
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
          nameResolver.variableNameForClassProperty(memberShape)
        );
    }
    if (
      StringUtils.equals(
        nameResolver.classPropertyForStructureMember(memberShape),
        "TargetValue"
      )
    ) {
      // value.TargetValue returns a double, the Api constructor needs is an int
      return "%s((int)value.%s)".formatted(
          typeConverterForShape(memberShape.getId(), TO_DAFNY),
          nameResolver.classPropertyForStructureMember(memberShape)
        );
    }
    if (
      ERROR_CTOR.contains(memberShape.getContainer().getName()) ||
      memberShape.getContainer().getName().endsWith("Error")
    ) {
      return "%s(value.getMessage())".formatted(
          typeConverterForShape(memberShape.getId(), TO_DAFNY)
        );
    }
    return "%s(value.%s)".formatted(
        typeConverterForShape(memberShape.getId(), TO_DAFNY),
        nameResolver.classPropertyForStructureMember(memberShape)
      );
  }

  // return true if this struct/member is one of the special ones with a IsXxxSet member
  public boolean memberSupportsIsSet(final MemberShape memberShape) {
    String parent = memberShape.getId().getName();
    String member = nameResolver.classPropertyForStructureMember(memberShape);
    if (parent.equals("ScanInput")) {
      if (
        member.equals("TotalSegments") ||
        member.equals("Segment") ||
        member.equals("Limit")
      ) {
        return true;
      }
    }
    if (parent.equals("QueryInput") && member.equals("Limit")) {
      return true;
    }
    return false;
  }

  /**
   * Returns:
   * "type varName = value.IsSetPropertyName() ? value.PropertyName : (type) null;"
   */
  public TokenTree generateExtractOptionalMember(
    final MemberShape memberShape
  ) {
    final String type = nameResolver.baseTypeForShape(memberShape.getId());
    final String varName = nameResolver.variableNameForClassProperty(
      memberShape
    );
    final String propertyName = nameResolver.classPropertyForStructureMember(
      memberShape
    );
    if (AwsSdkNameResolverHelpers.isInAwsSdkNamespace(memberShape.getId())) {
      if (memberSupportsIsSet(memberShape)) {
        final String isSetMember = nameResolver.isSetMemberForStructureMember(
          memberShape
        );
        return TokenTree.of(
          type,
          varName,
          "= value.%s".formatted(isSetMember),
          "? value.%s :".formatted(propertyName),
          "(%s) null;".formatted(type)
        );
      } else {
        return TokenTree.of(
          type,
          varName,
          "= value.%s != null".formatted(propertyName),
          "? value.%s :".formatted(propertyName),
          "(%s) null;".formatted(type)
        );
      }
    } else {
      final String isSetMethod = nameResolver.isSetMethodForStructureMember(
        memberShape
      );
      return TokenTree.of(
        type,
        varName,
        "= value.%s()".formatted(isSetMethod),
        "? value.%s :".formatted(propertyName),
        "(%s) null;".formatted(type)
      );
    }
  }

  public TypeConverter generateMemberConverter(final MemberShape memberShape) {
    final Shape targetShape = model.expectShape(memberShape.getTarget());

    final String targetFromDafnyConverterName = typeConverterForShape(
      targetShape.getId(),
      FROM_DAFNY
    );
    final String targetToDafnyConverterName = typeConverterForShape(
      targetShape.getId(),
      TO_DAFNY
    );

    if (!nameResolver.memberShapeIsOptional(memberShape)) {
      final TokenTree fromDafnyBody = Token.of(
        "return %s(value);".formatted(targetFromDafnyConverterName)
      );
      final TokenTree toDafnyBody = Token.of(
        "return %s(value);".formatted(targetToDafnyConverterName)
      );
      return buildConverterFromMethodBodies(
        memberShape,
        fromDafnyBody,
        toDafnyBody
      );
    }

    String cSharpTypeUnModified;
    if (
      StringUtils.equals(
        nameResolver.baseTypeForShape(targetShape.getId()),
        AwsSdkDotNetNameResolver.DDB_ATTRIBUTE_VALUE_MODEL_NAMESPACE
      )
    ) {
      cSharpTypeUnModified = AwsSdkDotNetNameResolver.DDB_V2_ATTRIBUTE_VALUE;
    } else {
      cSharpTypeUnModified = nameResolver.baseTypeForShape(memberShape.getId());
    }

    if (cSharpTypeUnModified.endsWith("?")) {
      cSharpTypeUnModified =
        cSharpTypeUnModified.substring(0, (cSharpTypeUnModified.length() - 1));
    }

    final String cSharpType = cSharpTypeUnModified;
    final String cSharpOptionType;
    if (
      StringUtils.equals(
        nameResolver.baseTypeForShape(memberShape.getId()),
        AwsSdkDotNetNameResolver.DDB_ATTRIBUTE_VALUE_MODEL_NAMESPACE
      )
    ) {
      cSharpOptionType = AwsSdkDotNetNameResolver.DDB_V2_ATTRIBUTE_VALUE;
    } else {
      cSharpOptionType = nameResolver.baseTypeForShape(memberShape.getId());
    }
    final String dafnyOptionType =
      nameResolver.dafnyConcreteTypeForOptionalMember(memberShape);
    final TokenTree fromDafnyBody = Token.of(
      "return value.is_None ? (%s) null : %s(value.Extract());".formatted(
          cSharpOptionType,
          targetFromDafnyConverterName
        )
    );
    final TokenTree toDafnyBody = Token.of(
      "return value == null ? %s.create_None() : %s.create_Some(%s((%s) value));".formatted(
          dafnyOptionType,
          dafnyOptionType,
          targetToDafnyConverterName,
          cSharpType
        )
    );
    return buildConverterFromMethodBodies(
      memberShape,
      fromDafnyBody,
      toDafnyBody
    );
  }

  public TypeConverter generateUnionConverter(final UnionShape unionShape) {
    final List<MemberShape> defNames = ModelUtils
      .streamUnionMembers(unionShape)
      .toList();
    final String unionClass;
    if (
      StringUtils.equals(
        nameResolver.baseTypeForShape(unionShape.getId()),
        AwsSdkDotNetNameResolver.DDB_ATTRIBUTE_VALUE_MODEL_NAMESPACE
      )
    ) {
      unionClass = AwsSdkDotNetNameResolver.DDB_V2_ATTRIBUTE_VALUE;
    } else {
      unionClass = nameResolver.baseTypeForShape(unionShape.getId());
    }
    final String dafnyUnionConcreteType =
      nameResolver.dafnyConcreteTypeForUnion(unionShape);
    final Token throwInvalidUnionState = Token.of(
      "\nthrow new System.ArgumentException(\"Invalid %s state\");".formatted(
          unionClass
        )
    );

    final TokenTree concreteVar = Token.of(
      "%1$s concrete = (%1$s)value;".formatted(dafnyUnionConcreteType)
    );
    final TokenTree convertedVar = Token.of(
      "var converted = new %s();".formatted(unionClass)
    );

    final TokenTree fromDafnyBody = TokenTree
      .of(
        defNames
          .stream()
          .map(memberShape -> {
            final String propertyName =
              nameResolver.classPropertyForStructureMember(memberShape);
            final String memberFromDafnyConverterName = typeConverterForShape(
              memberShape.getId(),
              FROM_DAFNY
            );
            final String destructorValue;
            if (
              StringUtils.equals(
                memberShape.getId().getName(),
                "AttributeValue"
              )
            ) {
              destructorValue =
                nameResolver.classPropertyForStructureMember(memberShape);
            } else {
              destructorValue =
                DafnyNameResolverHelpers.dafnyCompilesExtra_(
                  memberShape.getMemberName()
                );
            }
            return TokenTree
              .of(
                "if (value.is_%s)".formatted(
                    DafnyNameResolverHelpers.dafnyCompilesExtra_(
                      memberShape.getMemberName()
                    )
                  )
              )
              .append(
                TokenTree
                  .of(
                    "converted.%s = %s(concrete.dtor_%s);".formatted(
                        propertyName,
                        memberFromDafnyConverterName,
                        destructorValue
                      ),
                    "return converted;"
                  )
                  .lineSeparated()
                  .braced()
              );
          })
      )
      .prepend(TokenTree.of(concreteVar, convertedVar).lineSeparated())
      .append(throwInvalidUnionState);

    String validate = "value.Validate();";
    if (AwsSdkNameResolverHelpers.isInAwsSdkNamespace(unionShape.getId())) {
      validate = "";
    }
    final TokenTree toDafnyBody = TokenTree
      .of(
        TokenTree.of(validate),
        TokenTree.of(
          defNames
            .stream()
            .map(memberShape -> {
              final String propertyName =
                nameResolver.classPropertyForStructureMember(memberShape);
              final String propertyType =
                nameResolver.classPropertyTypeForStructureMember(memberShape);
              final String dafnyMemberName = nameResolver.unionMemberName(
                memberShape
              );
              final String memberFromDafnyConverterName = typeConverterForShape(
                memberShape.getId(),
                TO_DAFNY
              );
              // Dafny generates just "create" instead of "create_FOOBAR" if there's only one ctor
              String createSuffixUnMod = defNames.size() == 1
                ? ""
                : dafnyMemberName;
              // TODO come back and revisit how we generate Unions - we should use the names
              // defined in the smithy model
              // Wrt to the above TODO, we should also not handle Aws specific shapes here,
              // rather delegate it to the AwsSdkTypeConversionCodegen class.
              if (
                StringUtils.equals(
                  memberShape.getId().getName(),
                  "AttributeValue"
                ) ||
                StringUtils.equals(
                  memberShape.getContainer().getName(),
                  "Materials"
                )
              ) {
                createSuffixUnMod = "_%s".formatted(propertyName);
              }
              final String createSuffix = createSuffixUnMod;
              if (
                StringUtils.equals(
                  memberShape.getId().getName(),
                  "AttributeValue"
                )
              ) {
                final TokenTree checkIfValuePresent;

                // List<T> where T is not of type AttributeVale are always not null, but empty.
                final Set<String> listTypes = Set.of("BS", "NS", "SS");

                // When generating the toDafnyBody, there is an edge case for AttributeValue.
                // When checking if this a certain type the ddb sdk for net only gas value.is*Set for
                // lists, map, and boolean types - it does not have one for the remaining attribute union types
                final Set<String> checkedAttributeValues = Set.of(
                  "L",
                  "M",
                  "BOOL"
                );

                // In v2 of the net sdk for ddb the only Is%sSet apis are for L, M, or BOOL other unions do
                // not exist.
                if (checkedAttributeValues.contains(propertyName)) {
                  checkIfValuePresent =
                    TokenTree.of("if (value.Is%sSet)".formatted(propertyName));
                } else if (listTypes.contains(propertyName)) {
                  checkIfValuePresent =
                    TokenTree.of("if (value.%s.Any())".formatted(propertyName));
                } else if ("NULL".equals(propertyName)) {
                  checkIfValuePresent =
                    TokenTree.of(
                      "if (value.%s == true)".formatted(propertyName)
                    );
                } else {
                  checkIfValuePresent =
                    TokenTree.of(
                      "if (value.%s != null)".formatted(propertyName)
                    );
                }

                return checkIfValuePresent.append(
                  TokenTree
                    .of(
                      "return %s.create%s(%s(value.%s));".formatted(
                          dafnyUnionConcreteType,
                          createSuffix,
                          memberFromDafnyConverterName,
                          propertyName
                        )
                    )
                    .lineSeparated()
                    .braced()
                );
              } else {
                return TokenTree
                  .of("if (value.IsSet%s())".formatted(propertyName))
                  .append(
                    TokenTree
                      .of(
                        "return %s.create%s(%s(value.%s));".formatted(
                            dafnyUnionConcreteType,
                            createSuffix,
                            memberFromDafnyConverterName,
                            propertyName
                          )
                      )
                      .lineSeparated()
                      .braced()
                  );
              }
            })
        )
      )
      .append(throwInvalidUnionState);

    return buildConverterFromMethodBodies(
      unionShape,
      fromDafnyBody,
      toDafnyBody
    );
  }

  /**
   * This should not be called directly, instead call
   * {@link TypeConversionCodegen#generateStructureConverter(StructureShape)}.
   */
  protected TypeConverter generateReferenceStructureConverter(
    final StructureShape structureShape,
    final ReferenceTrait referenceTrait
  ) {
    final ShapeId referentId = referenceTrait.getReferentId();
    return switch (referenceTrait.getReferentType()) {
      case SERVICE -> generateServiceReferenceStructureConverter(
        structureShape,
        model.expectShape(referentId, ServiceShape.class)
      );
      case RESOURCE -> generateResourceReferenceStructureConverter(
        structureShape,
        model.expectShape(referentId, ResourceShape.class)
      );
    };
  }

  /**
   * This should not be called directly, instead call
   * {@link TypeConversionCodegen#generateStructureConverter(StructureShape)}.
   */
  protected TypeConverter generateServiceReferenceStructureConverter(
    final StructureShape structureShape,
    final ServiceShape serviceShape
  ) {
    // AWS SDK services are identified by namespace
    // TODO is this actually a good filter for AWS SDK services?
    if (serviceShape.getId().getNamespace().startsWith("com.amazonaws.")) {
      final AwsSdkTypeConversionCodegen awsSdkTypeConversionCodegen =
        new AwsSdkTypeConversionCodegen(model, serviceShape);
      final AwsSdkTypeConversionCodegen.DafnyConverterBodies dafnyConverterBodies =
        awsSdkTypeConversionCodegen.generateAwsSdkServiceReferenceStructureConverter(
          structureShape
        );
      return buildConverterFromMethodBodies(
        structureShape,
        dafnyConverterBodies.fromDafnyBody(),
        dafnyConverterBodies.toDafnyBody()
      );
      // Local services are identified by dependent shapes with a reference trait
    } else if (
      ModelUtils.isReferenceDependantModuleType(
        structureShape,
        serviceShape.getId().getNamespace()
      )
    ) {
      return generateLocalServiceReferenceStructureConverter(
        structureShape,
        serviceShape
      );
    } else {
      throw new UnsupportedOperationException(
        "Unsupported service shape: %s".formatted(serviceShape)
      );
    }
  }

  /**
   * This should not be called directly, instead call
   * {@link TypeConversionCodegen#generateStructureConverter(StructureShape)}.
   */
  protected TypeConverter generateLocalServiceReferenceStructureConverter(
    final StructureShape structureShape,
    final ServiceShape serviceShape
  ) {
    final ShapeId resourceShapeId = serviceShape.getId();
    final String baseType = nameResolver.baseTypeForShape(resourceShapeId);
    final String throwCustomImplException =
      "throw new System.ArgumentException(\"Custom implementations of %s are not supported yet\");".formatted(
          baseType
        );

    final TokenTree fromDafnyBody = Token.of(
      """
      if (value is %s dafnyValue) {
          return new %s(dafnyValue);
      }
      """.formatted(
          nameResolver.dafnyTypeForShape(serviceShape.getId()),
          baseType
        ),
      throwCustomImplException
    );

    final TokenTree toDafnyBody = Token.of(
      """
      if (value is %s nativeValue) {
          return nativeValue.%s();
      }
      """.formatted(baseType, ShimCodegen.SHIM_UMWRAP_METHOD_NAME),
      throwCustomImplException
    );

    return buildConverterFromMethodBodies(
      structureShape,
      fromDafnyBody,
      toDafnyBody
    );
  }

  /**
   * This should not be called directly, instead call
   * {@link TypeConversionCodegen#generateStructureConverter(StructureShape)}.
   */
  protected TypeConverter generateResourceReferenceStructureConverter(
    final StructureShape structureShape,
    final ResourceShape resourceShape
  ) {
    final ShapeId resourceShapeId = resourceShape.getId();
    final String shimClass = nameResolver.shimClassForResource(resourceShapeId);
    final String baseType = nameResolver.baseTypeForShape(resourceShapeId);
    if (!resourceShape.hasTrait(ExtendableTrait.class)) {
      final TokenTree fromDafnyBody = Token.of(
        "return new %s(value);".formatted(
            nameResolver.shimClassForResource(resourceShapeId)
          )
      );
      final TokenTree toDafnyBody = Token.of(
        """
        if (value is %s valueWithImpl) {
            return valueWithImpl._impl;
        }
        throw new System.ArgumentException("Custom implementations of %s are not supported");
        """.formatted(shimClass, baseType)
      );
      return buildConverterFromMethodBodies(
        structureShape,
        fromDafnyBody,
        toDafnyBody
      );
    }
    final String nativeWrapperClass =
      nameResolver.nativeWrapperClassForResource(resourceShapeId);
    final String baseClass = nameResolver.baseClassForResource(resourceShapeId);
    final TokenTree fromDafnyBody = Token.of(
      """
      if (value is %s nativeWrapper) return nativeWrapper._impl;
      return new %s(value);
      """.formatted(nativeWrapperClass, shimClass)
    );
    TokenTree cases = TokenTree.of(
      """
      case %s valueWithImpl:
          return valueWithImpl._impl;
      """.formatted(shimClass)
    );
    cases =
      cases.append(
        TokenTree.of(
          """
          case %s nativeImpl:
              return new %s(nativeImpl);
          """.formatted(baseClass, nativeWrapperClass)
        )
      );
    cases =
      cases.append(
        TokenTree.of(
          """
          default:
              throw new System.ArgumentException(
                  "Custom implementations of %s must extend %s.");""".formatted(
              shimClass,
              baseClass
            )
        )
      );
    final TokenTree toDafnyBody = Token
      .of("switch (value)")
      .append(cases.braced())
      .lineSeparated();
    return buildConverterFromMethodBodies(
      structureShape,
      fromDafnyBody,
      toDafnyBody
    );
  }

  /**
   * This should not be called directly, instead call
   * {@link TypeConversionCodegen#generateStructureConverter(StructureShape)}.
   */
  private TypeConverter generatePositionalStructureConverter(
    final StructureShape structureShape
  ) {
    final ShapeId memberShapeId = ModelUtils
      .getPositionalStructureMember(structureShape)
      .orElseThrow();

    final String memberFromDafnyConverterName = typeConverterForShape(
      memberShapeId,
      FROM_DAFNY
    );
    final String memberToDafnyConverterName = typeConverterForShape(
      memberShapeId,
      TO_DAFNY
    );
    final TokenTree fromDafnyBody = Token.of(
      "return %s(value);".formatted(memberFromDafnyConverterName)
    );
    final TokenTree toDafnyBody = Token.of(
      "return %s(value);".formatted(memberToDafnyConverterName)
    );

    return buildConverterFromMethodBodies(
      structureShape,
      fromDafnyBody,
      toDafnyBody
    );
  }

  /**
   * A pair of names for a {@link software.amazon.smithy.model.traits.EnumDefinition}, consisting of the
   * Smithy-defined name (the {@link EnumDefNames#defName}) and the Dafny-compiler-generated name (the
   * {@link EnumDefNames#dafnyName}).
   */
  private record EnumDefNames(String defName, String dafnyName) {}

  public TypeConverter generateEnumConverter(final EnumShape enumShape) {
    return generateEnumConverter(
      enumShape,
      enumShape.expectTrait(SyntheticEnumTrait.class)
    );
  }

  /**
   * This should not be called directly, instead call either
   * {@link TypeConversionCodegen#generateStringConverter(StringShape)} (for @enums)
   * or
   * {@link TypeConversionCodegen#generateEnumConverter(EnumShape)} (for Smithy 2.0 enums).
   */
  private TypeConverter generateEnumConverter(
    final Shape shape,
    final EnumTrait enumTrait
  ) {
    assert enumTrait.hasNames();
    //noinspection OptionalGetWithoutIsPresent
    final List<EnumDefNames> defNames = enumTrait
      .getValues()
      .stream()
      .map(enumDefinition -> enumDefinition.getName().get())
      .map(name ->
        new EnumDefNames(
          name,
          DotNetNameResolver.dafnyCompiledNameForEnumDefinitionName(name)
        )
      )
      .toList();
    final String enumClass = nameResolver.baseTypeForShape(shape.getId());
    final String dafnyEnumConcreteType = nameResolver.dafnyConcreteTypeForEnum(
      shape.getId()
    );
    final Token throwInvalidEnumValue = Token.of(
      "\nthrow new System.ArgumentException(\"Invalid %s value\");".formatted(
          enumClass
        )
    );

    final TokenTree fromDafnyBody = TokenTree
      .of(
        defNames
          .stream()
          .map(names ->
            "if (value.is_%s) return %s.%s;".formatted(
                names.dafnyName,
                enumClass,
                names.defName
              )
          )
          .map(Token::of)
      )
      .lineSeparated()
      .append(throwInvalidEnumValue);

    final TokenTree toDafnyBody = TokenTree
      .of(
        defNames
          .stream()
          .map(names -> {
            final String condition =
              "%s.%s.Equals(value)".formatted(enumClass, names.defName);
            // Dafny generates just "create" instead of "create_FOOBAR" if there's only one ctor
            final String createSuffix = defNames.size() == 1
              ? ""
              : "_%s".formatted(names.dafnyName);
            return "if (%s) return %s.create%s();".formatted(
                condition,
                dafnyEnumConcreteType,
                createSuffix
              );
          })
          .map(Token::of)
      )
      .lineSeparated()
      .append(throwInvalidEnumValue);

    return buildConverterFromMethodBodies(shape, fromDafnyBody, toDafnyBody);
  }

  /**
   * @see DafnyUtf8BytesTrait
   */
  private TypeConverter generateUtf8BytesConverter(
    final StringShape stringShape
  ) {
    final TokenTree fromDafnyBody = Token.of(
      """
      System.Text.UTF8Encoding utf8 = new System.Text.UTF8Encoding(false, true);
      return utf8.GetString(value.Elements);"""
    );
    final TokenTree toDafnyBody = Token.of(
      """
      System.Text.UTF8Encoding utf8 = new System.Text.UTF8Encoding(false, true);
      return Dafny.Sequence<byte>.FromArray(utf8.GetBytes(value));"""
    );
    return buildConverterFromMethodBodies(
      stringShape,
      fromDafnyBody,
      toDafnyBody
    );
  }

  // TODO: The javadoc below is outdated. The following is no longer true:
  //  "all of a Service's Exceptions descend from a root Service Exception"
  //  We should update this.
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
  // TODO: This is a run-on method. We SHOULD break it up into smaller pieces.
  public TypeConverter generateCommonExceptionConverter() {
    // Gather the Smithy Modeled specific exceptions by collecting them into a TreeSet.
    // This sorts the set by shape ID, making the order deterministic w.r.t the model.
    final TreeSet<StructureShape> errorShapes = getServiceErrors();

    // TODO: Is a raw exception really the right thing to be returning?
    final String dafnyType = DotNetNameResolver.dafnyTypeForCommonServiceError(
      serviceShape
    );

    final TokenTree fromDafnyBody = errorFromDanyBody(errorShapes);

    final TokenTree fromDafnyConverterSignature = Token.of(
      "public static %s %s(%s value)".formatted(
          C_SHARP_SYSTEM_EXCEPTION,
          nameResolver.typeConverterForCommonError(serviceShape, FROM_DAFNY),
          dafnyType
        )
    );
    final TokenTree fromDafnyConverterMethod = TokenTree.of(
      fromDafnyConverterSignature,
      fromDafnyBody.braced()
    );

    final TokenTree toDafnyBody = errorToDafnyBody(errorShapes);

    final TokenTree toDafnyConverterSignature = Token.of(
      "public static %s %s(System.Exception value)".formatted(
          dafnyType,
          nameResolver.typeConverterForCommonError(serviceShape, TO_DAFNY)
        )
    );
    final TokenTree toDafnyConverterMethod = TokenTree.of(
      toDafnyConverterSignature,
      toDafnyBody.braced()
    );

    // The Common Exception Converter is novel to Polymorph, it is not native to smithy.
    // As such, it needs a shape ID. That shape ID must not conflict with anything else.
    final ShapeId syntheticShapeId = ShapeId.fromParts(
      serviceShape.getId().getNamespace(),
      "__SYNTHETIC_COMMON_ERROR"
    );
    return new TypeConverter(
      syntheticShapeId,
      fromDafnyConverterMethod,
      toDafnyConverterMethod
    );
  }

  @Nonnull
  protected TreeSet<StructureShape> getServiceErrors() {
    final TreeSet<StructureShape> errorShapes = ModelUtils
      .streamServiceErrors(model, serviceShape)
      .collect(Collectors.toCollection(TreeSet::new));
    return errorShapes;
  }

  protected TokenTree errorFromDanyBody(
    final TreeSet<StructureShape> errorShapes
  ) {
    // Generate the FROM_DAFNY method
    // Handle dependency exceptions
    TokenTree dependencyErrorCasesFromDafny = TokenTree.empty();
    if (serviceShape.hasTrait(LocalServiceTrait.class)) {
      final LocalServiceTrait localServiceTrait = serviceShape.expectTrait(
        LocalServiceTrait.class
      );

      TreeSet<String> dependentNamespaces = new TreeSet<>(
        ModelUtils.findAllDependentNamespaces(
          new HashSet<>(Collections.singleton(localServiceTrait.getConfigId())),
          model
        )
      );

      if (localServiceTrait.getDependencies() != null) {
        localServiceTrait
          .getDependencies()
          .stream()
          .map(model::expectShape)
          .map(Shape::asServiceShape)
          .filter(Optional::isPresent)
          .map(Optional::get)
          .forEach(serviceShape ->
            dependentNamespaces.add(serviceShape.getId().getNamespace())
          );
      }

      if (dependentNamespaces.size() > 0) {
        Stream<TokenTree> cases = dependentNamespaces
          .stream()
          .map(dependentNamespace ->
            TokenTree.of(
              """
              case %1$s.Error_%3$s dafnyVal:
                return %2$s.TypeConversion.FromDafny_CommonError(
                  dafnyVal._%3$s
                );""".formatted(
                  DafnyNameResolverHelpers.dafnyExternNamespaceForShapeId(
                    serviceShape.getId()
                  ),
                  DotNetNameResolver.convertToCSharpNamespaceWithSegmentMapper(
                    dependentNamespace,
                    DotNetNameResolver::capitalizeNamespaceSegment
                  ),
                  DafnyNameResolver.dafnyBaseModuleName(dependentNamespace)
                )
            )
          );
        dependencyErrorCasesFromDafny = TokenTree.of(cases).lineSeparated();
      }
    }

    // Handle the modeled exceptions.
    final TokenTree modeledExceptionsFromDafny = TokenTree
      .of(
        errorShapes
          .stream()
          .map(errorShape -> {
            final ShapeId modeledErrorShapeId = errorShape.getId();
            return Token.of(
              "case %1$s dafnyVal:\nreturn %2$s(dafnyVal);".formatted(
                  nameResolver.dafnyTypeForShape(modeledErrorShapeId),
                  typeConverterForShape(modeledErrorShapeId, FROM_DAFNY)
                )
            );
          })
      )
      .lineSeparated();

    // Handle casting to the CollectionOfErrors list of exception type
    // TODO: replace `new string` with generic converter when
    //  conversion library for .NET is created.
    final TokenTree handleCollectionOfErrorsFromDafny = TokenTree
      .of(
        "case %1$s dafnyVal:".formatted(
            DotNetNameResolver.dafnyCollectionOfErrorsTypeForServiceShape(
              serviceShape
            )
          ),
        ("""
          return new %1$s(
               new System.Collections.Generic.List<Exception>(dafnyVal.dtor_list.CloneAsArray()
                 .Select(x => %2$s(x))),
               new string(dafnyVal.dtor_message.Elements));""").formatted(
            DotNetNameResolver.baseClassForCollectionOfErrors(),
            nameResolver.qualifiedTypeConverterForCommonError(
              serviceShape,
              FROM_DAFNY
            )
          )
      )
      .lineSeparated();

    // Handle the special cases that were cast to the root service exception.
    final TokenTree handleBaseFromDafny = TokenTree
      .of(
        "case %1$s dafnyVal:".formatted(
            DotNetNameResolver.dafnyUnknownErrorTypeForServiceShape(
              serviceShape
            )
          ),
        "return new %1$s(dafnyVal._obj);".formatted(
            DotNetNameResolver.baseClassForUnknownError()
          ),
        "case %1$s dafnyVal:".formatted(
            DotNetNameResolver.dafnyUnknownWithTextErrorTypeForServiceShape(
              serviceShape
            )
          ),
        "return new %1$s(dafnyVal._obj, dafnyVal._obj.ToString());".formatted(
            DotNetNameResolver.baseClassForUnknownWithTextError()
          ),
        "default:",
        "// The switch MUST be complete for _IError, so `value` MUST NOT be an _IError. (How did you get here?)",
        "return new %1$s();".formatted(
            DotNetNameResolver.baseClassForUnknownError()
          )
      )
      .lineSeparated();

    // Wrap all the converters into a switch statement.
    final TokenTree fromDafnySwitchCases = TokenTree
      .of(
        dependencyErrorCasesFromDafny,
        modeledExceptionsFromDafny,
        handleCollectionOfErrorsFromDafny,
        handleBaseFromDafny
      )
      .lineSeparated()
      .braced();
    final TokenTree fromDafnyBody = TokenTree
      .of(TokenTree.of("switch(value)"), fromDafnySwitchCases)
      .lineSeparated();
    return fromDafnyBody;
  }

  protected TokenTree errorToDafnyBody(
    final TreeSet<StructureShape> errorShapes
  ) {
    // Generate the TO_DAFNY method
    // Handle any dependencies first.
    // For errors from dependencies: pass anything from a dependency-recognized namespace into Dafny
    // This passes all unmodelled errors to the dependency type conversion
    TokenTree dependencyErrorsSwitchStatementToDafny = TokenTree.empty();
    if (serviceShape.hasTrait(LocalServiceTrait.class)) {
      final LocalServiceTrait localServiceTrait = serviceShape.expectTrait(
        LocalServiceTrait.class
      );

      Set<String> dependentNamespaces = ModelUtils.findAllDependentNamespaces(
        new HashSet<ShapeId>(
          Collections.singleton(localServiceTrait.getConfigId())
        ),
        model
      );

      // Dependencies may throw "unmodelled" errors that are unknown to Polymorph. Polymorph cannot write
      //   explicit code to handle these errors because it does not know about unmodelled errors.
      // This passes errors from a dependency-recognized namespace into the dependency's error handler.
      // This handles both modelled and unmodelled errors.
      TokenTree dependencyErrors = TokenTree.empty();
      if (dependentNamespaces.size() > 0) {
        List<TokenTree> casesList = new ArrayList<>();
        for (String dependentNamespace : dependentNamespaces) {
          TokenTree toAppend = TokenTree.of(
            """
            case "%1$s":
              return %2$s.Error.create_%3$s(
                %1$s.TypeConversion.ToDafny_CommonError(value)
              );""".formatted(
                DotNetNameResolver.convertToCSharpNamespaceWithSegmentMapper(
                  dependentNamespace,
                  DotNetNameResolver::capitalizeNamespaceSegment
                ),
                DafnyNameResolverHelpers.dafnyExternNamespaceForShapeId(
                  serviceShape.getId()
                ),
                DafnyNameResolver.dafnyBaseModuleName(dependentNamespace)
              )
          );
          casesList.add(toAppend);
        }

        final TokenTree casesTokens = TokenTree
          .of(casesList.stream())
          .lineSeparated();

        // This `switch` condition is based on the namespace of the exception, and not the specific exception type.
        dependencyErrorsSwitchStatementToDafny =
          Token
            .of("switch (value.GetType().Namespace)")
            .append(casesTokens.braced());
      }
    }

    // Handle the modeled exceptions.
    final TokenTree specificExceptionsToDafny = TokenTree
      .of(
        errorShapes
          .stream()
          .map(errorShape -> {
            final ShapeId specificErrorShapeId = errorShape.getId();
            return Token.of(
              "case %1$s exception:\n return %2$s(exception);".formatted(
                  nameResolver.baseTypeForShape(specificErrorShapeId),
                  typeConverterForShape(specificErrorShapeId, TO_DAFNY)
                )
            );
          })
      )
      .lineSeparated();

    final TokenTree handleCollectionOfErrorsToDafny = collectionOfErrorsToDafny(
      serviceShape,
      nameResolver
    );

    // Return the root service exception with the custom message.
    final TokenTree handleAnyExceptionToDafny = TokenTree
      .of(
        "// OpaqueError is redundant, but listed for completeness.",
        "case %1$s exception:".formatted(
            DotNetNameResolver.baseClassForUnknownError()
          ),
        "return new %1$s(exception);".formatted(
            DotNetNameResolver.dafnyUnknownErrorTypeForServiceShape(
              serviceShape
            )
          ),
        "case %1$s exception:".formatted(C_SHARP_SYSTEM_EXCEPTION),
        "return new %1$s(exception);".formatted(
            DotNetNameResolver.dafnyUnknownErrorTypeForServiceShape(
              serviceShape
            )
          ),
        "default:",
        "// The switch MUST be complete for System.Exception, so `value` MUST NOT be an System.Exception. (How did you get here?)",
        "return new %1$s(value);".formatted(
            DotNetNameResolver.dafnyUnknownErrorTypeForServiceShape(
              serviceShape
            )
          )
      )
      .lineSeparated();

    // Wrap all the converters into a switch statement.
    final TokenTree toDafnySwitchCases = TokenTree
      .of(
        specificExceptionsToDafny,
        handleCollectionOfErrorsToDafny,
        handleAnyExceptionToDafny
      )
      .lineSeparated()
      .braced();
    final TokenTree toDafnyBody = TokenTree
      .of(
        dependencyErrorsSwitchStatementToDafny,
        TokenTree.of("switch (value)"),
        toDafnySwitchCases
      )
      .lineSeparated();
    return toDafnyBody;
  }

  public static TokenTree collectionOfErrorsToDafny(
    ServiceShape serviceShape,
    DotNetNameResolver nameResolver
  ) {
    // Return CollectionOfErrors wrapper for list of exceptions.
    // String conversion must be hard coded as this method is used in
    // LocalServiceWrappedShimCodegen which may not have a sting converter!!
    // TODO: replace `Dafny.Sequence<char>.FromString` with generic converter when
    //  conversion library for .NET is created.
    return TokenTree
      .of(
        ("""
          case %1$s collectionOfErrors:
             return new %2$s(
               Dafny.Sequence<%3$s>
                 .FromArray(
                   collectionOfErrors.list.Select
                       (x => %4$s(x))
                     .ToArray()),
               Dafny.Sequence<char>.FromString(collectionOfErrors.Message)
             );""").formatted(
            DotNetNameResolver.baseClassForCollectionOfErrors(),
            DotNetNameResolver.dafnyCollectionOfErrorsTypeForServiceShape(
              serviceShape
            ),
            DotNetNameResolver.dafnyTypeForCommonServiceError(serviceShape),
            nameResolver.qualifiedTypeConverterForCommonError(
              serviceShape,
              TO_DAFNY
            )
          )
      )
      .lineSeparated();
  }

  /**
   * Returns a type converter for an {@code @error} structure.
   * <p>
   * This requires special-casing because a System.Exception's {@code message} field cannot be set by property, but
   * instead must be passed to the constructor.
   */
  public TypeConverter generateSpecificExceptionConverter(
    final StructureShape errorShape
  ) {
    assert errorShape.hasTrait(ErrorTrait.class);
    assert errorShape.getMember("message").isPresent();
    final ShapeId messageShapeId = errorShape.getId().withMember("message");

    final Token fromDafnyBody = Token.of(
      "return new %s(%s(value.Message));".formatted(
          nameResolver.baseTypeForShape(errorShape.getId()),
          typeConverterForShape(messageShapeId, FROM_DAFNY)
        )
    );
    final Token toDafnyBody = Token.of(
      """
      %1$s converted = new %1$s();
      converted.message = %2$s(value.Message);
      return converted;
      """.formatted(
          nameResolver.dafnyTypeForShape(errorShape.getId()),
          typeConverterForShape(messageShapeId, TO_DAFNY)
        )
    );

    return buildConverterFromMethodBodies(
      errorShape,
      fromDafnyBody,
      toDafnyBody
    );
  }

  /**
   * Returns a type converter for an {@code @error} structure.
   * <p>
   * This requires special-casing because a System.Exception's {@code message} field cannot be set by property, but
   * instead must be passed to the constructor.
   */
  public TypeConverter generateSpecificModeledErrorConverter(
    final StructureShape errorShape
  ) {
    assert errorShape.hasTrait(ErrorTrait.class);
    final String structureType = nameResolver.baseTypeForShape(
      errorShape.getId()
    );

    final TokenTree fromDafnyConstructorArgs = TokenTree
      .of(
        ModelUtils
          .streamStructureMembers(errorShape)
          .map(memberShape -> {
            final String dafnyMemberName = DotNetNameResolver.memberName(
              memberShape
            );
            final String memberFromDafnyConverterName = typeConverterForShape(
              memberShape.getId(),
              FROM_DAFNY
            );
            // special case for CancellationReasons Exception - this is the only exception
            // that throws a list of possible errors - these must be turned into a string and thrown as an exception
            // in order to be accepted by the API
            if (StringUtils.equals(dafnyMemberName, "_CancellationReasons")) {
              return Token.of(
                "new Exception(%s(value.%s).ToString())".formatted(
                    memberFromDafnyConverterName,
                    dafnyMemberName
                  )
              );
            } else {
              return Token.of(
                "%s(value.%s)".formatted(
                    memberFromDafnyConverterName,
                    dafnyMemberName
                  )
              );
            }
          })
      )
      .separated(Token.of(','))
      .lineSeparated();

    final TokenTree fromDafnyBody = TokenTree.of(
      Token.of("return new"),
      Token.of(structureType),
      fromDafnyConstructorArgs.parenthesized().lineSeparated(),
      Token.of(';')
    );

    final TokenTree toDafnyIsSetTernaries = TokenTree
      .of(
        ModelUtils
          .streamStructureMembers(errorShape)
          .filter(nameResolver::memberShapeIsOptional)
          .map(this::generateExtractOptionalMember)
      )
      .lineSeparated();
    final TokenTree toDafnyConstructorArgs = TokenTree
      .of(
        ModelUtils
          .streamStructureMembers(errorShape)
          .map(this::generateConstructorArg)
          .map(Token::of)
      )
      .separated(Token.of(','))
      .lineSeparated();
    final TokenTree toDafnyConstructor = TokenTree.of(
      TokenTree.of("return new"),
      TokenTree.of(nameResolver.dafnyConcreteTypeForErrorStructure(errorShape)),
      toDafnyConstructorArgs.parenthesized().lineSeparated(),
      Token.of(';')
    );

    final TokenTree toDafnyBody = TokenTree
      .of(toDafnyIsSetTernaries, toDafnyConstructor)
      .lineSeparated();

    return buildConverterFromMethodBodies(
      errorShape,
      fromDafnyBody,
      toDafnyBody
    );
  }

  /**
   * Build a {@link TypeConverter} by surrounding the given type converter method bodies with appropriate method
   * signatures. Each method body should assume the sole argument (the value to convert) is named {@code value}.
   */
  protected TypeConverter buildConverterFromMethodBodies(
    final Shape shape,
    final TokenTree fromDafnyBody,
    final TokenTree toDafnyBody
  ) {
    final ShapeId id = shape.getId();
    final String dafnyType = nameResolver.dafnyTypeForShape(id);
    String type;
    if (
      StringUtils.equals(
        nameResolver.baseTypeForShape(id),
        AwsSdkDotNetNameResolver.DDB_ATTRIBUTE_VALUE_MODEL_NAMESPACE
      )
    ) {
      type = AwsSdkDotNetNameResolver.DDB_V2_ATTRIBUTE_VALUE;
    } else {
      type = nameResolver.baseTypeForShape(id);
    }

    if (StringUtils.equals(type, "Amazon.DynamoDBv2.IAmazonDynamoDBv2")) {
      type = AwsSdkDotNetNameResolver.DDB_NET_INTERFACE_NAME;
    }

    // InvalidEndpointException was deprecated in v3 of the dynamodb sdk for net
    if (
      StringUtils.equals(
        type,
        "Amazon.DynamoDBv2.Model.InvalidEndpointException"
      )
    ) {
      return new TypeConverter(
        shape.getId(),
        TokenTree.of(""),
        TokenTree.of("")
      );
    }
    // Some DDB Modeled exceptions don't end in Exception and the SDK v3 for NET has all Exceptions
    // end with Exception known exceptions with this behavior are: RequestLimitExceeded, InternalServerError
    if (
      type.endsWith("RequestLimitExceeded") ||
      type.endsWith("InternalServerError")
    ) {
      type = "%sException".formatted(type);
    }
    final String cSharpType = type;

    // For any module that takes a dependency on this module,
    // they will need to wrap and unwrap reference types.
    // This is more controlled than exposing
    // the NativeWrapper and the Dafny wrapped type.
    final boolean isDependantModuleType =
      ModelUtils.isReferenceDependantModuleType(
        shape,
        nameResolver.namespaceForService()
      );

    // Make all converters public, because most need to be and it's not worth the trouble to hide the remaining few.
    final String visibility = "public";

    final String fromDafnyConverterName = typeConverterForShape(id, FROM_DAFNY);
    final TokenTree fromDafnyConverterSignature = TokenTree.of(
      "%s static".formatted(visibility),
      cSharpType,
      fromDafnyConverterName,
      "(%s value)".formatted(dafnyType)
    );

    final String toDafnyConverterName = typeConverterForShape(id, TO_DAFNY);
    final TokenTree toDafnyConverterSignature = TokenTree.of(
      "%s static".formatted(visibility),
      dafnyType,
      toDafnyConverterName,
      "(%s value)".formatted(cSharpType)
    );

    if (!isDependantModuleType) {
      final TokenTree fromDafnyConverterMethod = TokenTree.of(
        fromDafnyConverterSignature,
        fromDafnyBody.braced()
      );
      final TokenTree toDafnyConverterMethod = TokenTree.of(
        toDafnyConverterSignature,
        toDafnyBody.braced()
      );
      return new TypeConverter(
        shape.getId(),
        fromDafnyConverterMethod,
        toDafnyConverterMethod
      );
    } else {
      // This module is referencing a type from another module.
      // These referenced types are not be internal to this module.
      // Therefore, we need to call the conversion in the dependent module.
      final String namespaceForReferent = nameResolver.namespaceForShapeId(id);
      final TokenTree fromDafnyBodyOverride = TokenTree
        .of(
          "// This is converting a reference type in a dependant module.",
          "// Therefore it defers to the dependant module for conversion",
          "return %s.TypeConversion.%s(value);".formatted(
              namespaceForReferent,
              fromDafnyConverterName
            )
        )
        .lineSeparated();

      final TokenTree toDafnyBodyOverride = TokenTree
        .of(
          "// This is converting a reference type in a dependant module.",
          "// Therefore it defers to the dependant module for conversion",
          "return %s.TypeConversion.%s(value);".formatted(
              namespaceForReferent,
              toDafnyConverterName
            )
        )
        .lineSeparated();

      final TokenTree fromDafnyConverterMethod = TokenTree.of(
        fromDafnyConverterSignature,
        fromDafnyBodyOverride.braced()
      );
      final TokenTree toDafnyConverterMethod = TokenTree.of(
        toDafnyConverterSignature,
        toDafnyBodyOverride.braced()
      );
      return new TypeConverter(
        id,
        fromDafnyConverterMethod,
        toDafnyConverterMethod
      );
    }
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
