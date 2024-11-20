// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.utils;

import static software.amazon.polymorph.smithyjava.nameresolver.Constants.SMITHY_API_UNIT;

import java.util.*;
import java.util.regex.Pattern;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import software.amazon.polymorph.traits.ClientConfigTrait;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.traits.ExtendableTrait;
import software.amazon.polymorph.traits.JavaDocTrait;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.MutableLocalStateTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.codegen.core.TopologicalIndex;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.neighbor.Walker;
import software.amazon.smithy.model.shapes.*;
import software.amazon.smithy.model.traits.DocumentationTrait;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.RequiredTrait;
import software.amazon.smithy.model.traits.StringTrait;
import software.amazon.smithy.model.transform.ModelTransformer;

public class ModelUtils {

  // Require title-case alphanumeric names, so we don't need to check for keyword conflicts.
  //
  // The spec recommends a similar stricter definition for consistency (uppercase instead of title-case):
  // https://smithy.io/1.0/spec/core/constraint-traits.html?highlight=enum#enum-trait
  private static final Pattern ENUM_NAME_PATTERN = Pattern.compile(
    "^[A-Za-z_0-9]*$"
  );

  /**
   * Adds our custom traits (and their definitions) to a {@link ModelAssembler}.
   * <p>
   * Note that this only needs to be called if the model file(s) being processed do not define these traits
   * (for example, in unit tests). If the model file does define the traits, adding them again does nothing.
   */
  public static void addCustomTraitsToModelAssembler(
    final ModelAssembler assembler
  ) {
    assembler.addShape(ReferenceTrait.getDefinition());
    assembler.addShape(PositionalTrait.getDefinition());
    assembler.addShape(ClientConfigTrait.getDefinition());
    assembler.addShape(DafnyUtf8BytesTrait.getDefinition());
    assembler.addShape(ExtendableTrait.getDefinition());
    LocalServiceTrait.getDefinitions().forEach(assembler::addShape);
    assembler.addShape(MutableLocalStateTrait.getDefinition());
    assembler.addShape(JavaDocTrait.getDefinition());
  }

  /**
   * @return a stream of members of the given structure shape
   */
  public static Stream<MemberShape> streamStructureMembers(
    final StructureShape structureShape
  ) {
    return structureShape.getAllMembers().values().stream();
  }

  /**
   * @return a stream of members of the given structure shape, sorted by name
   */
  public static Stream<MemberShape> streamStructureMembersSorted(
    final StructureShape structureShape
  ) {
    return structureShape
      .getAllMembers()
      .entrySet()
      .stream()
      .sorted(Map.Entry.comparingByKey())
      .map(Map.Entry::getValue);
  }

  public static Stream<MemberShape> streamUnionMembers(
    final UnionShape unionShape
  ) {
    return unionShape.getAllMembers().values().stream();
  }

  /**
   * @return a stream of error structures in the given service shape
   */
  public static Stream<StructureShape> streamServiceErrors(
    final Model model,
    final ServiceShape serviceShape
  ) {
    return streamNamespaceErrors(model, serviceShape.getId().getNamespace());
  }

  /**
   * @return a stream of error structures in the given namespace
   */
  public static Stream<StructureShape> streamNamespaceErrors(
    final Model model,
    final String namespace
  ) {
    // Collect into TreeSet so that we generate code in a deterministic order (lexicographic, in particular)
    return new TreeSet<>(model.getStructureShapesWithTrait(ErrorTrait.class))
      .stream()
      .filter(structureShape ->
        structureShape.getId().getNamespace().equals(namespace)
      );
  }

  /**
   * Returns a stream of enum shapes in the given namespace.
   * These include both Smithy v2 enums,
   * and Smithy v1 @enum strings converted to {@link EnumShape}s.
   */
  public static Stream<EnumShape> streamEnumShapes(
    final Model model,
    final String namespace
  ) {
    @SuppressWarnings("deprecation")
    final Stream<EnumShape> v1Enums = model
      .getStringShapesWithTrait(EnumTrait.class)
      .stream()
      .map(ModelUtils::stringToEnumShape);
    final Stream<EnumShape> v2Enums = model.getEnumShapes().stream();
    return Stream
      .concat(v1Enums, v2Enums)
      .filter(shape -> shape.getId().getNamespace().equals(namespace));
  }

  public static EnumShape stringToEnumShape(final StringShape stringShape) {
    return EnumShape
      .fromStringShape(stringShape)
      .orElseThrow(() ->
        new UnsupportedOperationException(
          "Could not convert %s to an enum".formatted(stringShape.getId())
        )
      );
  }

  /**
   * @return true if the given shape ID is in the given service's namespace
   */
  public static boolean isInServiceNamespace(
    final ToShapeId shapeId,
    final ServiceShape serviceShape
  ) {
    return shapeId
      .toShapeId()
      .getNamespace()
      .equals(serviceShape.getId().getNamespace());
  }

  /**
   * Returns the sole member of the given positional structure shape, or {@link Optional#empty()} if the given shape
   * isn't a positional structure.
   */
  public static Optional<ShapeId> getPositionalStructureMember(
    final Shape shape
  ) {
    if (!shape.hasTrait(PositionalTrait.class)) {
      return Optional.empty();
    }

    if (shape.members().size() != 1) {
      // For now, we only intend this trait to be used for operation returns, so we therefore only allow one
      // member. Eventually if we also want to use this to unwrap operation inputs (or any more general
      // unwrapping) we'll need to relax this constraint.
      throw new IllegalStateException(
        "Structures marked with '@positional' must have exactly one member"
      );
    }

    //noinspection OptionalGetWithoutIsPresent
    final MemberShape memberShape = shape.members().stream().findFirst().get();
    return Optional.of(memberShape.getId());
  }

  public static boolean memberShapeIsOptional(
    final Model model,
    final MemberShape memberShape
  ) {
    final Shape containerShape = model.expectShape(memberShape.getContainer());
    return (
      containerShape.isStructureShape() &&
      !containerShape.hasTrait(PositionalTrait.class) &&
      !memberShape.isRequired()
    );
  }

  /**
   * Returns true if the given shape ID is in the {@code smithy.api} namespace, or false otherwise.
   */
  public static boolean isSmithyApiShape(final ShapeId shapeId) {
    return shapeId.getNamespace().equals("smithy.api");
  }

  public static boolean isValidEnumDefinitionName(final String name) {
    return ENUM_NAME_PATTERN.matcher(name).matches();
  }

  /**
   * Like {@link ModelUtils#validateErrorStructureMessageNotRequired(StructureShape)}, but with the
   * added constraint that the {@code message} member must have the {@code @required} trait applied.
   */
  public static void validateErrorStructureMessageRequired(
    final StructureShape structureShape
  ) {
    validateErrorStructureMessageNotRequired(structureShape);

    boolean messageRequired = structureShape
      .getMember("message")
      .filter(member -> member.hasTrait(RequiredTrait.class))
      .isPresent();
    if (!messageRequired) {
      throw new IllegalArgumentException(
        "The 'message' member of %s must be @required".formatted(
            structureShape.getId()
          )
      );
    }
  }

  /**
   * @return the service in a given namespace
   */
  public static ServiceShape serviceFromNamespace(
    final Model model,
    final String namespace
  ) {
    final ServiceShape[] tmp = model
      .getServiceShapes()
      .stream()
      .filter(s -> s.toShapeId().getNamespace().equals(namespace))
      .toArray(ServiceShape[]::new);

    if (tmp.length != 1) {
      throw new IllegalStateException(
        "Found " +
        tmp.length +
        " services matching " +
        namespace +
        ", need exactly one"
      );
    }

    return tmp[0];
  }

  /**
   * Throws {@link IllegalArgumentException} unless the given structure shape satisfies code-generation constraints:
   * <ul>
   *     <li>The structure must have the {@code @error} trait applied</li>
   *     <li>The structure must have a {@code message} member</li>
   *     <li>The structure must not have any members except {@code message}</li>
   * </ul>
   */
  public static void validateErrorStructureMessageNotRequired(
    final StructureShape structureShape
  ) {
    if (!structureShape.hasTrait(ErrorTrait.class)) {
      throw new IllegalArgumentException(
        "%s is not an @error structure".formatted(structureShape.getId())
      );
    }

    boolean hasMessage = structureShape.getMember("message").isPresent();
    if (!hasMessage) {
      throw new IllegalArgumentException(
        "Error structure %s is missing a 'message' member".formatted(
            structureShape.getId()
          )
      );
    }

    // TODO support other members
    if (structureShape.getMemberNames().size() > 1) {
      throw new IllegalArgumentException(
        "Error structure %s cannot have members other than 'message'".formatted(
            structureShape.getId()
          )
      );
    }
  }

  private static final Pattern TRAILING_FACTORY_PATTERN = Pattern.compile(
    "Factory$"
  );

  /**
   * If the given string ends with "Factory" and has at least one character prior, returns a copy of the string
   * without the trailing "Factory". Otherwise, returns a copy of the string with no modifications.
   */
  private static String stripTrailingFactory(final CharSequence s) {
    return TRAILING_FACTORY_PATTERN
      .matcher(s)
      // exclude the first char
      .region(1, s.length())
      .replaceFirst("");
  }

  /**
   * Returns the given service's name without the trailing "Factory", if it exists; otherwise returns the service's
   * name unmodified.
   */
  public static String serviceNameWithoutTrailingFactory(
    final ServiceShape serviceShape
  ) {
    return stripTrailingFactory(serviceShape.getId().getName());
  }

  public static boolean isSmithyApiOrSimpleShape(Shape shape) {
    // Special Enum case
    if (shape.hasTrait(EnumTrait.class)) {
      return false;
    }
    if (isSmithyApiShape(shape.getId())) {
      return true;
    }
    return shape.getType().getCategory().equals(ShapeType.Category.SIMPLE);
  }

  /**
   * For every ShapeId in {@code initialShapes},
   * with the given {@code model},
   * find all the member shapes with @reference traits that ShapeId depends on.
   */
  public static Set<MemberShape> findAllDependentMemberReferenceShapes(
    Set<ShapeId> initialShapeIds,
    Model model
  ) {
    Set<ShapeId> dependentShapes = findAllDependentShapes(
      initialShapeIds,
      model
    );
    return dependentShapes
      .stream()
      .map(shapeId -> model.expectShape(shapeId, Shape.class))
      .filter(shape -> shape.asMemberShape().isPresent())
      .map(shape -> shape.asMemberShape().get())
      .filter(shape ->
        model
          .expectShape(shape.getTarget(), Shape.class)
          .hasTrait(ReferenceTrait.class)
      )
      .collect(Collectors.toSet());
  }

  public static Set<String> findAllDependentNamespaces(
    Set<ShapeId> initialShapeIds,
    Model model
  ) {
    // Set of all namespaces from all initialShapeIds
    Set<String> initialNamespaces = initialShapeIds
      .stream()
      .map(ShapeId::getNamespace)
      .collect(Collectors.toSet());

    Set<ShapeId> dependentShapeIds = findAllDependentShapes(
      initialShapeIds,
      model
    );

    // Set of all namespaces in dependentShapeIds that are not in initialNamespaces
    return dependentShapeIds
      .stream()
      .map(ShapeId::getNamespace)
      .filter(namespace -> !initialNamespaces.contains(namespace))
      // smithy.api is technically a dependent namespace, as models depend on Smithy API.
      // However, we are not interested in it as a dependent namespace for our purposes.
      .filter(namespace -> !namespace.equals("smithy.api"))
      .collect(Collectors.toSet());
  }

  /**
   * For every ShapeId in {@code initialShapes},
   * with the given {@code model},
   * find all the shapes that ShapeId depends on.
   */
  public static Set<ShapeId> findAllDependentShapes(
    Set<ShapeId> initialShapeIds,
    Model model
  ) {
    final Set<ShapeId> shapes = new LinkedHashSet<>();
    // Breadth-first search via getDependencyShapeIds
    final Queue<ShapeId> toTraverse = new LinkedList<>(initialShapeIds);
    while (!toTraverse.isEmpty()) {
      final ShapeId currentShapeId = toTraverse.remove();
      if (shapes.add(currentShapeId)) {
        final Shape currentShape = model.expectShape(currentShapeId);
        getDependencyShapeIds(currentShape).forEach(toTraverse::add);
      }
    }
    return shapes;
  }

  /**
   * For every ShapeId in {@code initialShapes},
   * with the given {@code model},
   * return a list of shape IDs where:
   *  - The first element is the initial shape ID
   *  - The last element is the shape ID of a reference shape
   *  - Intermediate elements are a path of shapes from the first to the last shape ID
   *    such that l[i] is a dependent shape of l[i-1].
   */
  public static Set<
    List<ShapeId>
  > findAllDependentMemberReferenceShapesWithPaths(
    Set<ShapeId> initialShapeIds,
    Model model
  ) {
    Set<List<ShapeId>> outList = new LinkedHashSet<>(new ArrayList<>());

    Set<List<ShapeId>> dependentShapesWithPaths =
      findAllDependentShapesWithPaths(initialShapeIds, model);
    for (List<ShapeId> dependentShapeWithPath : dependentShapesWithPaths) {
      ShapeId finalDependentShapeId = dependentShapeWithPath.get(
        dependentShapeWithPath.size() - 1
      );
      Shape finalDependentShape = model.expectShape(
        finalDependentShapeId,
        Shape.class
      );
      if (finalDependentShape.asMemberShape().isPresent()) {
        MemberShape finalDependentShapeAsMember = finalDependentShape
          .asMemberShape()
          .get();
        if (
          model
            .expectShape(finalDependentShapeAsMember.getTarget(), Shape.class)
            .hasTrait(ReferenceTrait.class)
        ) {
          outList.add(dependentShapeWithPath);
        }
      }
    }

    return outList;
  }

  /**
   * For every ShapeId in {@code initialShapes},
   * with the given {@code model},
   * return a list of shape IDs where:
   *  - The first element is the initial shape ID
   *  - The last element is the shape ID of a reference shape
   *  - Intermediate elements are a path of shapes from the first to the last shape ID
   */
  public static Set<List<ShapeId>> findAllDependentShapesWithPaths(
    Set<ShapeId> initialShapeIds,
    Model model
  ) {
    Set<List<ShapeId>> initialShapeIdsAsPaths = initialShapeIds
      .stream()
      .map(Collections::singletonList)
      .collect(Collectors.toSet());
    Set<List<ShapeId>> pathsToShapes = new LinkedHashSet<>(
      new LinkedHashSet<>()
    );

    // Breadth-first search via getDependencyShapeIds
    final Queue<List<ShapeId>> toTraverse = new LinkedList<>(
      initialShapeIdsAsPaths
    );
    while (!toTraverse.isEmpty()) {
      final List<ShapeId> currentShapeIdWithPath = toTraverse.remove();

      if (pathsToShapes.add(currentShapeIdWithPath)) {
        final Shape currentShape = model.expectShape(
          currentShapeIdWithPath.get(currentShapeIdWithPath.size() - 1)
        );
        final List<List<ShapeId>> dependencyShapeIdsWithPaths =
          getDependencyShapeIds(currentShape)
            // to avoid cycles, append only those dependencyShapeId which are not already in the path currentShapeIdWithPath
            .filter(dependencyShapeId ->
              !currentShapeIdWithPath.contains(dependencyShapeId)
            )
            .map(dependencyShapeId ->
              Stream
                .concat(
                  currentShapeIdWithPath.stream(),
                  Stream.of(dependencyShapeId)
                )
                .toList()
            )
            .toList();
        dependencyShapeIdsWithPaths.forEach(toTraverse::add);
      }
    }
    return pathsToShapes;
  }

  /**
   * Returns dependency shape IDs for the given shape.
   * A shape {@code S} has a dependency shape {@code D} if a type
   * for {@code S} requires the existence of a type for {@code D}.
   */
  @SuppressWarnings("OptionalGetWithoutIsPresent")
  static Stream<ShapeId> getDependencyShapeIds(final Shape shape) {
    return switch (shape.getType()) {
      case LIST -> Stream.of(shape.asListShape().get().getMember().getId());
      case SET -> Stream.of(shape.asSetShape().get().getMember().getId());
      case MAP -> {
        final MapShape mapShape = shape.asMapShape().get();
        yield Stream.of(mapShape.getKey().getId(), mapShape.getValue().getId());
      }
      case STRUCTURE -> streamStructureMembers(shape.asStructureShape().get())
        .map(Shape::getId);
      case MEMBER -> Stream.of(shape.asMemberShape().get().getTarget());
      case UNION -> streamUnionMembers(shape.asUnionShape().get())
        .map(Shape::getId);
      default -> Stream.empty();
    };
  }

  @SuppressWarnings("OptionalGetWithoutIsPresent")
  public static boolean isListOrSetOfEnums(ShapeId shapeId, Model model) {
    Shape shape = model.expectShape(shapeId);
    return switch (shape.getType()) {
      case LIST -> isEnum(
        shape.asListShape().get().getMember().getTarget(),
        model
      );
      case SET -> isEnum(
        shape.asSetShape().get().getMember().getTarget(),
        model
      );
      default -> false;
    };
  }

  public static boolean isEnum(ShapeId shapeId, Model model) {
    Shape shape = model.expectShape(shapeId);
    return shape.hasTrait(EnumTrait.class);
  }

  /*
        A reference type will point to a resource or service.
        Regardless of where this referent is
        the structure with the reference trait dictates
        where the native wrapper types will exist.
        If a Smithy namespace exports a service,
        that namespace may not export a reference type
        to support passing that service as an argument.
        Therefore, a namespace that needs to accept such a service
        needs to create a reference type that points to this service.

        This is why the function check to see if the shapes has a reference trait,
        but then compares the shapes' namespace and not the referent shape.
     */
  public static Boolean isReferenceDependantModuleType(
    final Shape shape,
    final String namespace
  ) {
    if (shape.hasTrait(ReferenceTrait.class)) {
      return isDependantModuleType(shape, namespace);
    } else {
      return false;
    }
  }

  public static Boolean isDependantModuleType(
    final Shape shape,
    final String namespace
  ) {
    final String shapeNamespace = shape.getId().getNamespace();
    if (!shapeNamespace.toLowerCase().startsWith("smithy.api") && !namespace.equalsIgnoreCase(shapeNamespace)) {
      return true;
    } else {
      return false;
    }
  }

  public static ShapeId checkForPositional(ShapeId originalId, Model model) {
    Shape originalShape = model.expectShape(originalId);
    if (originalShape.hasTrait(PositionalTrait.class)) {
      // Positional traits can only be on structures,
      // asStructureShape cannot return an empty optional
      //noinspection OptionalGetWithoutIsPresent
      MemberShape onlyMember = PositionalTrait.onlyMember(
        originalShape.asStructureShape().get()
      );
      return onlyMember.getTarget();
    }
    return originalId;
  }

  /**
   * @param toShapeId ToShapeId that might have positional or reference trait
   * @return Fully de-referenced shapeId and naive shapeId as a ResolvedShapeId
   */
  public static ResolvedShapeId resolveShape(ToShapeId toShapeId, Model model) {
    final ShapeId shapeId = toShapeId.toShapeId();
    if (shapeId.equals(SMITHY_API_UNIT)) {
      return new ResolvedShapeId(shapeId, shapeId);
    }
    ShapeId notPositionalId = checkForPositional(shapeId, model);
    if (model.expectShape(notPositionalId).hasTrait(ReferenceTrait.class)) {
      ReferenceTrait reference = model
        .expectShape(notPositionalId)
        .expectTrait(ReferenceTrait.class);
      return new ResolvedShapeId(shapeId, reference.getReferentId());
    }
    return new ResolvedShapeId(shapeId, notPositionalId);
  }

  /**
   * @param naiveId ShapeId that might have positional or reference trait.
   * @param resolvedId Fully de-referenced shapeId;
   *                   de-referenced means Positional or
   *                   Reference traits have been fully resolved.
   */
  public record ResolvedShapeId(ShapeId naiveId, ShapeId resolvedId) {}

  /**
   * Adds a "message: String" member to any structure with the error trait
   * that doesn't already define one (via case-insensitive match).
   */
  public static Model addMissingErrorMessageMembers(Model model) {
    return ModelTransformer
      .create()
      .mapShapes(
        model,
        shape -> {
          if (
            shape instanceof StructureShape && shape.hasTrait(ErrorTrait.class)
          ) {
            StructureShape errorShape = (StructureShape) shape;
            if (
              errorShape
                .members()
                .stream()
                .noneMatch(m -> "message".equalsIgnoreCase(m.getMemberName()))
            ) {
              MemberShape implicitMessageMember = MemberShape
                .builder()
                .id(errorShape.getId().withMember("message"))
                .target(ShapeId.from("smithy.api#String"))
                .build();
              return errorShape
                .toBuilder()
                .addMember(implicitMessageMember)
                .build();
            }
          }
          return shape;
        }
      );
  }

  /**
   * Return a builder for the provided shape.
   * @param shape
   * @return
   */
  public static AbstractShapeBuilder<?, ?> getBuilderForShape(Shape shape) {
    // This is painful, but there is nothing like `shape.getUnderlyingShapeType`...
    // instead, check every possible shape for its builder...
    AbstractShapeBuilder<?, ?> builder;
    if (shape.isBlobShape()) {
      builder = shape.asBlobShape().get().toBuilder();
    } else if (shape.isBooleanShape()) {
      builder = shape.asBooleanShape().get().toBuilder();
    } else if (shape.isDocumentShape()) {
      builder = shape.asDocumentShape().get().toBuilder();
    } else if (shape.isStringShape()) {
      builder = shape.asStringShape().get().toBuilder();
    } else if (shape.isTimestampShape()) {
      builder = shape.asTimestampShape().get().toBuilder();
    } else if (shape.isByteShape()) {
      builder = shape.asByteShape().get().toBuilder();
    } else if (shape.isIntegerShape()) {
      builder = shape.asIntegerShape().get().toBuilder();
    } else if (shape.isFloatShape()) {
      builder = shape.asFloatShape().get().toBuilder();
    } else if (shape.isBigIntegerShape()) {
      builder = shape.asBigIntegerShape().get().toBuilder();
    } else if (shape.isShortShape()) {
      builder = shape.asShortShape().get().toBuilder();
    } else if (shape.isLongShape()) {
      builder = shape.asLongShape().get().toBuilder();
    } else if (shape.isDoubleShape()) {
      builder = shape.asDoubleShape().get().toBuilder();
    } else if (shape.isBigDecimalShape()) {
      builder = shape.asBigDecimalShape().get().toBuilder();
    } else if (shape.isListShape()) {
      builder = shape.asListShape().get().toBuilder();
    } else if (shape.isSetShape()) {
      builder = shape.asSetShape().get().toBuilder();
    } else if (shape.isMapShape()) {
      builder = shape.asMapShape().get().toBuilder();
    } else if (shape.isStructureShape()) {
      builder = shape.asStructureShape().get().toBuilder();
    } else if (shape.isUnionShape()) {
      builder = shape.asUnionShape().get().toBuilder();
    } else if (shape.isServiceShape()) {
      builder = shape.asServiceShape().get().toBuilder();
    } else if (shape.isOperationShape()) {
      builder = shape.asOperationShape().get().toBuilder();
    } else if (shape.isResourceShape()) {
      builder = shape.asResourceShape().get().toBuilder();
    } else if (shape.isMemberShape()) {
      builder = shape.asMemberShape().get().toBuilder();
    } else if (shape.isEnumShape()) {
      builder = shape.asEnumShape().get().toBuilder();
    } else if (shape.isIntEnumShape()) {
      builder = shape.asIntEnumShape().get().toBuilder();
    } else {
      // Unfortunately, there is no "default" shape...
      // The above should cover all shapes; if not, new shapes need to be added above.
      throw new IllegalArgumentException(
        "Unable to process @javadoc trait on unsupported shape type: " + shape
      );
    }
    return builder;
  }

  public static Optional<String> getDocumentationOrJavadoc(Shape shape) {
    return shape
      .getTrait(DocumentationTrait.class)
      .map(StringTrait::getValue)
      .or(() -> shape.getTrait(JavaDocTrait.class).map(StringTrait::getValue));
  }

  public static List<Shape> getTopologicallyOrderedOrphanedShapesForService(
    ServiceShape serviceShape,
    Model model
  ) {
    // Copy-paste Smithy-Core's shape discovery mechanism:
    // Walk the model starting from the serviceShape.
    // This generates shapes that are "known" to Smithy-Core's `generateShapesInService`.
    Set<Shape> nonOrphanedShapes = new Walker(model).walkShapes(serviceShape);

    // orphanedShapes = (all shapes in model) - (non-orphaned shapes)
    Set<Shape> orphanedShapes = model.shapes().collect(Collectors.toSet());
    orphanedShapes.removeAll(nonOrphanedShapes);

    // Copy-paste Smithy-Core's shape ordering mechanism for topological ordering
    // (Python needs topological ordering to write shapes in order; other languages might not matter)
    List<Shape> orderedShapes = new ArrayList();

    TopologicalIndex topologicalIndex = TopologicalIndex.of(model);

    // Get orphaned shapes under the following conditions:
    // 1. In the same namespace as the service. (Should only generate shapes in this service.)
    // 2. Not a member shape. (Member shapes don't have their own shapes generated for them.)
    for (Shape shape : topologicalIndex.getOrderedShapes()) {
      if (
        orphanedShapes.contains(shape) &&
        ModelUtils.isInServiceNamespace(shape, serviceShape) &&
        !shape.isMemberShape()
      ) {
        orderedShapes.add(shape);
      }
    }
    for (Shape shape : topologicalIndex.getRecursiveShapes()) {
      if (
        orphanedShapes.contains(shape) &&
        ModelUtils.isInServiceNamespace(shape, serviceShape) &&
        !shape.isMemberShape()
      ) {
        orderedShapes.add(shape);
      }
    }

    return orderedShapes;
  }

  public static Stream<ServiceShape> streamLocalServiceDependencies(
    final Model model,
    final ServiceShape serviceShape
  ) {
    final Optional<LocalServiceTrait> localServiceTrait = serviceShape.getTrait(
      LocalServiceTrait.class
    );
    if (!localServiceTrait.isPresent()) {
      return Stream.empty();
    }

    final Set<ShapeId> dependentIds = localServiceTrait.get().getDependencies();
    if (dependentIds == null) {
      return Stream.empty();
    }

    return dependentIds
      .stream()
      .map(id -> model.expectShape(id, ServiceShape.class));
  }

  public static StructureShape getConfigShape(
    final Model model,
    final ServiceShape serviceShape
  ) {
    final Optional<LocalServiceTrait> localServiceTrait = serviceShape.getTrait(
      LocalServiceTrait.class
    );
    return model.expectShape(
      localServiceTrait.get().getConfigId(),
      StructureShape.class
    );
  }
}
