package software.amazon.polymorph.smithygo.localservice.nameresolver;

import static software.amazon.polymorph.smithygo.localservice.nameresolver.Constants.DOT;

import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeType;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.model.traits.EnumTrait;

public class DafnyNameResolver {

  public static String dafnyTypesNamespace(final Shape shape) {
    // Delegate to the smithy-dafny-dafny logic. Ideally, this should be independent, but it is not today.
    return software.amazon.polymorph.smithydafny.DafnyNameResolver.dafnyTypesModuleName(
      shape.toShapeId().getNamespace()
    );
  }

  public static String dafnyDependentErrorName(final Shape shape) {
    return software.amazon.polymorph.smithydafny.DafnyNameResolver.dafnyBaseModuleName(
      shape.toShapeId().getNamespace()
    );
  }

  public static String dafnyNamespace(final Shape shape) {
    return software.amazon.polymorph.smithydafny.DafnyNameResolver.dafnyBaseModuleName(
      shape.toShapeId().getNamespace()
    );
  }

  public static String dafnyNamespace(final ServiceTrait serviceTrait) {
    return software.amazon.polymorph.smithydafny.DafnyNameResolver.dafnyBaseModuleName(
      serviceTrait.getSdkId()
    );
  }

  public static String dafnyNamespace(
    final LocalServiceTrait localServiceTrait
  ) {
    return software.amazon.polymorph.smithydafny.DafnyNameResolver.dafnyBaseModuleName(
      localServiceTrait.getSdkId()
    );
  }

  /**
   * Returns the Dafny type for a given Shape.
   *
   * @param shape The Shape for which the Dafny type needs to be determined.
   * @param symbol The Symbol representing the Shape.
   * @return The Dafny type as a String.
   */
  public static String getDafnyType(final Shape shape, final Symbol symbol) {
    ShapeType type = shape.getType();
    if (shape.hasTrait(EnumTrait.class)) {
      type = ShapeType.ENUM;
    }
    switch (type) {
      case INTEGER, LONG, BOOLEAN:
        return dafnyCompilesExtra_(symbol.getName());
      case MAP:
        return "dafny.Map";
      // TODO: Figure out the dafny type for TIMESTAMP
      case DOUBLE, STRING, BLOB, LIST, TIMESTAMP:
        return "dafny.Sequence";
      case RESOURCE:
        return DafnyNameResolver
          .dafnyTypesNamespace(shape)
          .concat(DOT)
          .concat("I")
          .concat(dafnyCompilesExtra_(shape.toShapeId().getName()));
      // ENUM, STRUCTURE, UNION can be removed but for posterity it looks great to see all the shapes being covered.
      case ENUM, STRUCTURE, UNION:
      default:
        return DafnyNameResolver
          .dafnyTypesNamespace(shape)
          .concat(DOT)
          .concat(dafnyCompilesExtra_(symbol.getName()));
    }
  }

  public static String getDafnySubErrorType(
    final Shape shape,
    final Symbol symbol
  ) {
    return DafnyNameResolver
      .getDafnyBaseErrorType(shape)
      .concat("_")
      .concat(dafnyCompilesExtra_(symbol.getName()));
  }

  public static String getDafnyBaseErrorType(final Shape shape) {
    return DafnyNameResolver
      .dafnyTypesNamespace(shape)
      .concat(DOT)
      .concat("Error");
  }

  public static String getDafnyCompanionType(
    final Shape shape,
    final Symbol symbol
  ) {
    return DafnyNameResolver
      .dafnyTypesNamespace(shape)
      .concat(DOT)
      .concat("Companion_%s_".formatted(dafnyCompilesExtra_(symbol.getName())));
  }

  public static String getDafnyErrorCompanion(final Shape shape) {
    return DafnyNameResolver
      .dafnyTypesNamespace(shape)
      .concat(DOT)
      .concat("Companion_Error_");
  }

  public static String getDafnyErrorCompanionCreate(
    final Shape shape,
    final Symbol symbol
  ) {
    return DafnyNameResolver
      .getDafnyErrorCompanion(shape)
      .concat(DOT)
      .concat("Create_%s_".formatted(dafnyCompilesExtra_(symbol.getName())));
  }

  public static String getDafnyCompanionStructType(
    final Shape shape,
    final Symbol symbol
  ) {
    return DafnyNameResolver
      .dafnyTypesNamespace(shape)
      .concat(DOT)
      .concat(
        "CompanionStruct_%s_".formatted(dafnyCompilesExtra_(symbol.getName()))
      );
  }

  public static String getDafnyCompanionStructType(
    final Shape shape,
    final String memberName
  ) {
    return DafnyNameResolver
      .dafnyTypesNamespace(shape)
      .concat(DOT)
      .concat("CompanionStruct_%s_".formatted(dafnyCompilesExtra_(memberName)));
  }

  public static String getDafnyCompanionTypeCreate(
    final Shape shape,
    final Symbol symbol
  ) {
    return DafnyNameResolver
      .getDafnyCompanionType(shape, symbol)
      .concat(DOT)
      .concat("Create_%s_".formatted(dafnyCompilesExtra_(symbol.getName())));
  }

  /**
   * Returns the path to Create_ function for creating member shape within a union shape.
   *
   * @param unionShape The union shape containing the member shape.
   * @param memberName The name of the member shape within the union shape.
   */
  public static String getDafnyCreateFuncForUnionMemberShape(
    final UnionShape unionShape,
    final String memberName
  ) {
    return DafnyNameResolver
      .getDafnyUnionBaseStructType(unionShape, unionShape.getId().getName())
      .concat(DOT)
      .concat("Create_%s_".formatted(dafnyCompilesExtra_(memberName)));
  }

  public static String getDafnyClient(final String sdkId) {
    return sdkId.concat(DOT).concat(sdkId).concat("Client");
  }

  public static String getDafnyClientName(final String sdkId) {
    return sdkId.concat("Client");
  }

  public static String getDafnyInterfaceClient(final Shape shape) {
    return DafnyNameResolver
      .dafnyTypesNamespace(shape)
      .concat(DOT)
      .concat("I")
      .concat(shape.toShapeId().getName())
      .concat("Client");
  }

  public static String getDafnyInterfaceClient(
    final ServiceShape serviceShape,
    final ServiceTrait awsSdkServiceTrait
  ) {
    return DafnyNameResolver
      .dafnyTypesNamespace(serviceShape)
      .concat(DOT)
      .concat("I")
      .concat(awsSdkServiceTrait.getSdkId())
      .concat("Client");
  }

  public static String createDafnyClient(
    final Shape shape,
    final String sdkId
  ) {
    return sdkId.concat(".Companion_Default___").concat(DOT).concat(sdkId);
  }

  public static String getDafnyDependentErrorType(
    final Shape shape,
    final String sdkId
  ) {
    return DafnyNameResolver
      .dafnyNamespace(shape)
      .concat(".Companion_Default___")
      .concat(DOT)
      .concat(sdkId);
  }

  public static String getDafnyUnionBaseStructType(
    final Shape shape,
    final String memberName
  ) {
    return DafnyNameResolver
      .getDafnyCompanionStructType(shape, memberName)
      .concat("{}");
  }

  public static String dafnyCompilesExtra_(final String name) {
    return name.replace("_", "__");
  }
}
