package software.amazon.polymorph.smithygo.localservice.nameresolver;

import static software.amazon.polymorph.smithygo.localservice.nameresolver.Constants.BLANK;
import static software.amazon.polymorph.smithygo.localservice.nameresolver.Constants.DOT;

import java.util.Arrays;
import java.util.HashSet;
import java.util.Map;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;

public class SmithyNameResolver {

  private static Map<String, String> smithyNamespaceToGoModuleNameMap;
  // Known native type of simple shapes
  private static HashSet<String> knownSmithyType = new HashSet<>(
    Arrays.asList(
      "int32", //integer shape
      "string", // string shape
      "[]byte", // blob shape
      "int64", // long shape
      "float64", // double shape
      "bool" //boolean shape
    )
  );
  private static String awsServiceClientName = "Client";

  public static Boolean isShapeFromAWSSDK(final Shape shape) {
    // Is there a better way to do this?
    // I did not figure out any other then hardcoding.
    return shape.toShapeId().getNamespace().startsWith("com.amazonaws.");
  }

  public static void setSmithyNamespaceToGoModuleNameMap(
    Map<String, String> smithyNamespaceToGoModuleNameMap
  ) {
    SmithyNameResolver.smithyNamespaceToGoModuleNameMap =
      smithyNamespaceToGoModuleNameMap;
  }

  public static String getGoModuleNameForSmithyNamespace(
    final String smithyNamespace
  ) {
    if (smithyNamespace.contains("smithy.")) return "";
    if (!smithyNamespaceToGoModuleNameMap.containsKey(smithyNamespace)) {
      throw new IllegalArgumentException(
        "Go module name not found for Smithy namespace: " + smithyNamespace
      );
    }
    return smithyNamespaceToGoModuleNameMap.get(smithyNamespace);
  }

  public static String shapeNamespace(final Shape shape) {
    return shape
      .toShapeId()
      .getNamespace()
      .replace(DOT, BLANK)
      .toLowerCase()
      .concat("smithygenerated");
  }

  public static String smithyTypesNamespace(
    final Shape shape,
    final Model model
  ) {
    final String shapeNameSpace = shape.toShapeId().getNamespace();
    if (isShapeFromAWSSDK(shape)) {
      final String sdkName = shapeNameSpace
        .substring(shapeNameSpace.lastIndexOf(".") + 1)
        .toLowerCase();
      if (shape.hasTrait(ServiceTrait.class)) {
        return sdkName;
      }
      // Boolean to hold if shape is input or output of any operation
      boolean isTopLevelShape = model
        .shapes(OperationShape.class)
        .anyMatch(op ->
          op.getInput().filter(shape.getId()::equals).isPresent() ||
          op.getOutput().filter(shape.getId()::equals).isPresent()
        );
      return isTopLevelShape ? sdkName : sdkName.concat("types");
    }
    return shape
      .toShapeId()
      .getNamespace()
      .replace(DOT, BLANK)
      .toLowerCase()
      .concat("smithygeneratedtypes");
  }

  public static String getGoModuleNameForSdkNamespace(
    final String smithyNamespace
  ) {
    return getGoModuleNameForSmithyNamespace("sdk.".concat(smithyNamespace));
  }

  public static String smithyTypesNamespaceAws(
    final ServiceTrait serviceTrait,
    boolean isAwsSubType
  ) {
    if (isAwsSubType) {
      return "types";
    }
    return serviceTrait.getSdkId().toLowerCase();
  }

  public static String getSmithyType(
    final Shape shape,
    final Symbol symbol,
    final Model model
  ) {
    if (
      symbol.getNamespace().contains("smithy.") ||
      symbol.getNamespace().equals("smithyapitypes") ||
      knownSmithyType.contains(symbol.getName())
    ) {
      return symbol.getName();
    }
    if (shape.isResourceShape()) {
      return SmithyNameResolver
        .smithyTypesNamespace(shape, model)
        .concat(DOT)
        .concat("I")
        .concat(shape.toShapeId().getName());
    }
    // TODO: Figure out the type of timestamp
    if (shape.isTimestampShape()) {
      return "time".concat(DOT).concat(symbol.getName());
    }
    return SmithyNameResolver
      .smithyTypesNamespace(shape, model)
      .concat(DOT)
      .concat(symbol.getName());
  }

  public static String getSmithyType(final Shape shape, Model model) {
    return SmithyNameResolver
      .smithyTypesNamespace(shape, model)
      .concat(DOT)
      .concat(shape.toShapeId().getName());
  }

  public static String getSmithyTypeAws(
    final ServiceTrait serviceTrait,
    final Symbol symbol,
    boolean subtype
  ) {
    if (
      symbol.getNamespace().contains("smithy.") ||
      symbol.getNamespace().equals("smithyapitypes") ||
      knownSmithyType.contains(symbol.getName())
    ) {
      return symbol.getName();
    }
    // TODO: Figure types of Timestamp shape after completing timestamps
    if (symbol.getFullName().equals("time.Time")) {
      return (symbol.getFullName());
    }
    return SmithyNameResolver
      .smithyTypesNamespaceAws(serviceTrait, subtype)
      .concat(DOT)
      .concat(symbol.getName());
  }

  public static String getToDafnyMethodName(
    final ServiceShape serviceShape,
    final Shape shape,
    final String disambiguator
  ) {
    final var methodName = serviceShape
      .getContextualName(shape)
      .concat("_ToDafny");
    if (
      serviceShape
        .toShapeId()
        .getNamespace()
        .equals(shape.toShapeId().getNamespace())
    ) {
      return methodName;
    } else {
      return SmithyNameResolver
        .shapeNamespace(shape)
        .concat(DOT)
        .concat(methodName);
    }
  }

  public static String getToDafnyMethodName(
    final Shape shape,
    final String disambiguator
  ) {
    final var methodName = shape.getId().getName().concat("_ToDafny");
    return SmithyNameResolver
      .shapeNamespace(shape)
      .concat(DOT)
      .concat(methodName);
  }

  public static String getFromDafnyMethodName(
    final ServiceShape serviceShape,
    final Shape shape,
    final String disambiguator
  ) {
    final var methodName = serviceShape
      .getContextualName(shape)
      .concat("_FromDafny");
    if (
      serviceShape
        .toShapeId()
        .getNamespace()
        .equals(shape.toShapeId().getNamespace())
    ) {
      return methodName;
    } else {
      return SmithyNameResolver
        .shapeNamespace(shape)
        .concat(DOT)
        .concat(methodName);
    }
  }

  public static String getFromDafnyMethodName(
    final Shape shape,
    final String disambiguator
  ) {
    final var methodName = shape.getId().getName().concat("_FromDafny");
    return SmithyNameResolver
      .shapeNamespace(shape)
      .concat(DOT)
      .concat(methodName);
  }

  public static String getAwsServiceClient(final ServiceTrait serviceTrait) {
    return SmithyNameResolver
      .smithyTypesNamespaceAws(serviceTrait, false)
      .concat(DOT)
      .concat(getAwsServiceClientName());
  }

  public static String getAwsServiceClientName() {
    return awsServiceClientName;
  }
}
