package software.amazon.polymorph.smithygo.localservice.nameresolver;

import static software.amazon.polymorph.smithygo.localservice.nameresolver.Constants.BLANK;
import static software.amazon.polymorph.smithygo.localservice.nameresolver.Constants.DOT;
import static software.amazon.polymorph.smithygo.localservice.nameresolver.Constants.INTERNAL_DAFNY;
import static software.amazon.polymorph.smithygo.localservice.nameresolver.Constants.INTERNAL_DAFNY_TYPES;

import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeType;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.SensitiveTrait;
import software.amazon.smithy.utils.CaseUtils;

public class DafnyNameResolver {

  public static String dafnyTypesNamespace(final Shape shape) {
    return(CaseUtils.toPascalCase(shape
    .toShapeId()
    .getNamespace()
    .replace(DOT, " ")));
    // return shape
    //   .toShapeId()
    //   .getNamespace()
    //   .replace(DOT, BLANK)
    //   .toLowerCase()
    //   .concat(INTERNAL_DAFNY_TYPES);
  }

  public static String dafnyNamespace(final Shape shape) {
    return shape
      .toShapeId()
      .getNamespace()
      .replace(DOT, BLANK)
      .toLowerCase()
      .concat(INTERNAL_DAFNY);
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
        return symbol.getName();
      case MAP:
        return "dafny.Map";
      case DOUBLE, STRING, BLOB, LIST:
        return "dafny.Sequence";
      // default catches a case where users may author their own classes that implement and extend resource (ExtendableTrait)
      // ENUM, STRUCTURE, UNION can be removed but for posterity it looks great to see all the shapes being covered.
      case ENUM, STRUCTURE, UNION:
      default:
        return DafnyNameResolver
          .dafnyTypesNamespace(shape)
          .concat(DOT)
          .concat(symbol.getName())
          .concat("_smithygenerated");
    }
  }

  public static String getDafnySubErrorType(
    final Shape shape,
    final Symbol symbol
  ) {
    return DafnyNameResolver
      .getDafnyBaseErrorType(shape)
      .concat("_")
      .concat(symbol.getName());
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
      .concat("Companion_%s_".formatted(symbol.getName()));
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
      .concat("Create_%s_".formatted(symbol.getName()));
  }

  public static String getDafnyCompanionStructType(
    final Shape shape,
    final Symbol symbol
  ) {
    return DafnyNameResolver
      .dafnyTypesNamespace(shape)
      .concat(DOT)
      .concat("CompanionStruct_%s_".formatted(symbol.getName()));
  }

  public static String getDafnyCompanionTypeCreate(
    final Shape shape,
    final Symbol symbol
  ) {
    return DafnyNameResolver
      .getDafnyCompanionType(shape, symbol)
      .concat(DOT)
      .concat("Create_%s_".formatted(symbol.getName()));
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
    return "companion".concat(DOT)
      .concat(
        memberName.replace(unionShape.getId().getName() + "Member", "Create_")
      )
      .concat("_");
  }

  public static String getDafnyClient(final Shape shape, final String sdkId) {
    return DafnyNameResolver
      .dafnyNamespace(shape)
      .concat(DOT)
      .concat(sdkId)
      .concat("Client");
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
    return DafnyNameResolver
      .dafnyNamespace(shape)
      .concat(".Companion_Default___")
      .concat(DOT)
      .concat(sdkId);
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
}
