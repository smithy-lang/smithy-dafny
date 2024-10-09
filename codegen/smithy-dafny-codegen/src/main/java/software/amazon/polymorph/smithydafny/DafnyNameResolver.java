// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydafny;

import com.google.common.base.Joiner;
import java.nio.file.Path;
import java.util.*;
import java.util.stream.Stream;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import software.amazon.polymorph.smithyjava.NamespaceHelper;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.Token;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.*;
import software.amazon.smithy.model.traits.ReadonlyTrait;
import software.amazon.smithy.utils.StringUtils;

public record DafnyNameResolver(
  Model model,
  String namespace,
  // Collect into TreeSet so that we generate code in a deterministic order (lexicographic, in particular)
  TreeSet<DependentSmithyModel> dependentModels,
  Path[] dependentModelPaths
) {
  public static final Map<ShapeType, String> DAFNY_TYPES_BY_SIMPLE_SHAPE_TYPE =
    Map.ofEntries(
      Map.entry(ShapeType.BLOB, "seq<uint8>"),
      Map.entry(ShapeType.BOOLEAN, "bool"),
      Map.entry(ShapeType.STRING, "string"),
      // currently unused in model and unsupported in StandardLibrary.UInt
      //            Map.entry(ShapeType.BYTE, "int8"),
      //            Map.entry(ShapeType.SHORT, "int16"),
      Map.entry(ShapeType.INTEGER, "int32"),
      Map.entry(ShapeType.LONG, "int64"),
      Map.entry(ShapeType.DOUBLE, "seq<uint8>"),
      // TODO create/use better timestamp type in Dafny libraries
      Map.entry(ShapeType.TIMESTAMP, "string")
    );

  public static String nameForService(final ServiceShape serviceShape) {
    // If the service is an AWS SDK service, use the sdkId.
    // Otherwise, just use the shape name.
    return serviceShape
      .getTrait(ServiceTrait.class)
      .map(t -> AwsSdkNameResolverHelpers.mungeSdkId(t.getSdkId()))
      // TODO: LocalServiceTrait has an SDKID as well... is this wrong?
      .orElse(StringUtils.capitalize(serviceShape.getId().getName()));
  }

  @SuppressWarnings("OptionalGetWithoutIsPresent")
  public String baseTypeForShape(final ShapeId shapeId) {
    final Shape shape = model.expectShape(shapeId);
    final String shapeName = shapeId.getName();

    if (ModelUtils.isSmithyApiShape(shapeId)) {
      @Nullable
      final String simpleShapeType = DAFNY_TYPES_BY_SIMPLE_SHAPE_TYPE.get(
        shape.getType()
      );
      return Objects.requireNonNull(
        simpleShapeType,
        () -> String.format("No Dafny type for prelude shape %s", shapeId)
      );
    }

    return switch (shape.getType()) {
      case BLOB,
        BOOLEAN,
        STRING,
        ENUM,
        // currently unused in model and unsupported in StandardLibrary.UInt
        // BYTE, SHORT
        INTEGER,
        LONG,
        DOUBLE,
        LIST,
        MAP -> dafnyModulePrefixForShape(shape) + shapeName;
      case STRUCTURE -> {
        if (shape.hasTrait(ReferenceTrait.class)) {
          yield baseTypeForShape(
            shape.expectTrait(ReferenceTrait.class).getReferentId()
          );
        } else if (shape.hasTrait(PositionalTrait.class)) {
          final StructureShape structure = shape.asStructureShape().get();
          if (structure.getMemberNames().size() != 1) {
            throw new IllegalStateException(
              "Positional trait only supports a single member."
            );
          }
          final MemberShape member = structure
            .getMember(structure.getMemberNames().get(0))
            .get();
          yield baseTypeForShape(member.getTarget());
        } else {
          yield dafnyTypeNameShape(shape);
        }
      }
      case SERVICE -> traitForServiceClient(shape.asServiceShape().get());
      case RESOURCE -> traitForResource(shape.asResourceShape().get());
      // Member calls baseTypeForShape on their type
      case MEMBER -> baseTypeForMember(shape.asMemberShape().get());
      case UNION -> dafnyTypeNameShape(shape);
      // TODO create/use better timestamp type in Dafny libraries
      case TIMESTAMP -> "string";
      default -> throw new UnsupportedOperationException(
        "Shape %s has unsupported type %s".formatted(shapeId, shape.getType())
      );
    };
  }

  private String baseTypeForMember(final MemberShape memberShape) {
    final String targetType = baseTypeForShape(memberShape.getTarget());

    if (!ModelUtils.memberShapeIsOptional(model, memberShape)) {
      return targetType;
    }

    return ("Option<%s>").formatted(targetType);
  }

  private String dafnyTypeNameShape(final Shape shape) {
    return dafnyModulePrefixForShape(shape) + shape.getId().getName();
  }

  public String generatedTypeForShape(final ShapeId shapeId) {
    return StringUtils.capitalize(shapeId.getName());
  }

  public static String traitNameForServiceClient(
    final ServiceShape serviceShape
  ) {
    return "I%sClient".formatted(nameForService(serviceShape));
  }

  public String traitForServiceClient(final ServiceShape serviceShape) {
    return (
      dafnyModulePrefixForShape(serviceShape) +
      traitNameForServiceClient(serviceShape)
    );
  }

  public static String classNameForServiceClient(ServiceShape shape) {
    String serviceName = nameForService(shape);
    if (shape.hasTrait(LocalServiceTrait.class)) {
      LocalServiceTrait trait = shape.expectTrait(LocalServiceTrait.class);
      serviceName = trait.getSdkId();
    }
    return "%sClient".formatted(serviceName);
  }

  public String traitForResource(final ResourceShape resourceShape) {
    return (
      dafnyModulePrefixForShape(resourceShape) +
      traitNameForResource(resourceShape)
    );
  }

  public static String traitNameForResource(final ResourceShape shape) {
    final String resourceName = StringUtils.capitalize(shape.getId().getName());
    return "I%s".formatted(resourceName);
  }

  public String publicMethodNameForOperation(
    final OperationShape operationShape
  ) {
    return StringUtils.capitalize(operationShape.getId().getName());
  }

  public String methodNameToImplementForResourceOperation(
    final OperationShape operationShape
  ) {
    return "%s'".formatted(publicMethodNameForOperation(operationShape));
  }

  public String historicalCallEventsForOperation(
    final OperationShape operationShape
  ) {
    // This works because the history is stored in its own object
    return publicMethodNameForOperation(operationShape);
  }

  public String historicalCallHistoryClassForResource(
    final ResourceShape resource
  ) {
    return "%s%s".formatted(
        baseTypeForShape(resource.getId()),
        historicalCallHistoryPostfix()
      );
  }

  public String historicalCallHistoryClassForService(
    final ServiceShape service
  ) {
    return "%s%s".formatted(
        baseTypeForShape(service.getId()),
        historicalCallHistoryPostfix()
      );
  }

  public Boolean isFunction(
    final ServiceShape serviceShape,
    final OperationShape operationShape
  ) {
    // Operations that are declared as `@readOnly`
    // on services that are `@localService`
    // are treated as Dafny functions.
    // This is useful for proof.
    // Most languages do not have such a strict
    // no side effects mathematical construct.
    return (
      serviceShape.hasTrait(LocalServiceTrait.class) &&
      operationShape.hasTrait(ReadonlyTrait.class)
    );
  }

  public String executableType(
    final ServiceShape serviceShape,
    final OperationShape operationShape
  ) {
    return isFunction(serviceShape, operationShape)
      ? "function method"
      : "method";
  }

  public String ensuresPubliclyPredicate(final OperationShape operationShape) {
    return "%sEnsuresPublicly".formatted(
        publicMethodNameForOperation(operationShape)
      );
  }

  /**
   * Returns the return type for an operation of this service.
   * This is {@code Result<T, errorType>},
   * where {@code T} is either...
   * <ul>
   *     <li>... the corresponding Dafny output type, if the operation has output.</li>
   *     <li>... {@code ()} ("unit"), if the operation does not have output.</li>
   * </ul>
   */
  public String returnTypeForOperation(final OperationShape operationShape) {
    final String outputType = operationShape
      .getOutput()
      .map(this::baseTypeForShape)
      .orElse("()");
    return "Result<%s, %s>".formatted(outputType, "Error");
  }

  public Optional<String> returnTypeForResult(
    final OperationShape operationShape
  ) {
    if (operationShape.getOutput().isPresent()) {
      return Optional.of(
        this.baseTypeForShape(operationShape.getOutput().get())
      );
    }
    return Optional.empty();
  }

  public String validityPredicateForShape(final ShapeId shapeId) {
    final String unqualifiedTypeName = baseTypeForShape(shapeId);
    return "IsValid_%s".formatted(unqualifiedTypeName);
  }

  //TODO: Figure which of these public static string methods should go to DafnyNameResolverHelpers

  // i.e. "AwsCryptographyMaterialProvidersTypes"
  // This is the Dafny module name for the smithy->Dafny types file.
  public static String dafnyTypesModuleName(final String namespace) {
    return dafnyBaseModuleName(namespace) + "Types";
  }

  // i.e. "AwsCryptographyMaterialProviders"
  // This is used as a base to build various names for generated Dafny types and traits.
  public static String dafnyBaseModuleName(final String namespace) {
    final Stream<String> namespaceParts = Arrays
      .stream(namespace.split("\\."))
      .map(StringUtils::capitalize);
    return Joiner.on("").join(namespaceParts.iterator());
  }

  public String dafnyModulePrefixForShape(final Shape shape) {
    final String shapeNamespace = shape.getId().getNamespace();
    if (!namespace.equals(shapeNamespace)) {
      // Unfortunate side effect
      // Need to add these so that they can be included
      // because we are obviously using them!
      dependentModels.add(DependentSmithyModel.of(shape, dependentModelPaths));

      // Append `.` so that it is easy to use.
      // If you only want the name use localDafnyModuleName
      return dafnyTypesModuleName(shapeNamespace) + ".";
    } else {
      // This is "local" and so does not need any Module name...
      return "";
    }
  }

  /**
   * Outside of {@code smithydafny}, this should not be called directly.
   * Instead, call
   * {@link software.amazon.polymorph.utils.DafnyNameResolverHelpers#packageNameForNamespace}.
   */
  // i.e. "software.amazon.cryptography.materialproviders.internaldafny"
  // The base namespace at which all smithy->Dafny->X generated code is built to,
  // used in {:extern}.
  // TODO: Currently converts the smithy namespace into a Java idiomatic one.
  public static String dafnyExternNamespace(final String namespace) {
    return NamespaceHelper.standardize(namespace) + ".internaldafny";
  }

  /**
   * Outside of {@code smithydafny}, this should not be called directly.
   * Instead, call
   * {@link software.amazon.polymorph.utils.DafnyNameResolverHelpers#dafnyExternNamespaceForNamespace}.
   */
  // i.e. "software.amazon.cryptography.materialproviders.internaldafny.types"
  // The namespace for all the smithy->Dafny->X generated types,
  // i.e. the {:extern} for the Dafny Types module
  public static String dafnyTypesModuleExternNamespace(final String namespace) {
    return dafnyExternNamespace(namespace) + ".types";
  }

  public String callEventTypeName() {
    return "DafnyCallEvent";
  }

  public String mutableStateFunctionName() {
    return "Modifies";
  }

  public String dynamicMutableStateFunctionName() {
    return "InternalModifies";
  }

  public String validStateInvariantName() {
    return "ValidState";
  }

  public String dynamicValidStateInvariantName() {
    return "InternalValidState";
  }

  public String callHistoryFieldName() {
    return "History";
  }

  public String historicalCallHistoryPostfix() {
    return "CallHistory";
  }

  public static Stream<String> modulePreludeStandardImports() {
    return Stream.of(
      "import opened Wrappers",
      "import opened StandardLibrary.UInt",
      "import opened UTF8"
    );
  }

  public static Stream<TokenTree> abstractModulePrelude(
    ServiceShape serviceShape
  ) {
    final String typesModuleName = dafnyTypesModuleName(
      serviceShape.getId().getNamespace()
    );

    return Stream
      .concat(
        modulePreludeStandardImports(),
        Stream.of("import opened Types = %s".formatted(typesModuleName))
      )
      .map(i -> Token.of(i));
  }

  public static String abstractServiceModuleName(ServiceShape serviceShape) {
    final String moduleNamespace = moduleNamespace(
      serviceShape.getId().getNamespace()
    );
    return "Abstract%sService".formatted(moduleNamespace);
  }

  // TODO: I am so confused by what all these dafny*Namespace methods are doing.
  //  There has to be duplication. I do not know where. But it must exist.
  //  Let's give them documentation and then reduce.
  /** "com.amazonaws.kms" -> "ComAmazonAwsKms" */
  @Nonnull
  public static String moduleNamespace(String namespace) {
    return DafnyNameResolver.dafnyBaseModuleName(namespace);
  }

  public static String abstractOperationsModuleName(ServiceShape serviceShape) {
    final String moduleNamespace = moduleNamespace(
      serviceShape.getId().getNamespace()
    );
    return "Abstract%sOperations".formatted(moduleNamespace);
  }

  public static Stream<TokenTree> wrappedAbstractModulePrelude(
    ServiceShape serviceShape
  ) {
    return Stream.concat(
      abstractModulePrelude(serviceShape),
      Stream.of(
        TokenTree.of(
          "import WrappedService : %s".formatted(
              abstractServiceModuleName(serviceShape)
            )
        )
      )
    );
  }

  public static String internalConfigType() {
    return "InternalConfig";
  }

  public static String validConfigPredicate() {
    return "Valid%s?".formatted(internalConfigType());
  }

  public static String modifiesInternalConfig() {
    return "ModifiesInternalConfig";
  }
}
