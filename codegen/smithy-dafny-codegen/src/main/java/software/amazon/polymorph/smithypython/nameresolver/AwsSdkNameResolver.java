package software.amazon.polymorph.smithypython.nameresolver;

import java.util.Locale;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/**
 * Contains utility functions that map Smithy shapes
 * to useful strings used in Smithy-Python generated code.
 */
public class AwsSdkNameResolver {

  /**
   * Returns the name of the Smithy-generated client for the provided serviceShape.
   * The serviceShape SHOULD be a localService.
   * ex. example.namespace.ExampleService -> "ExampleServiceClient"
   * @param serviceShape
   * @return
   */
  public static String clientForService(ServiceShape serviceShape) {
      // TODO: Hardcode (ex) Trent -> KMS?
      if (serviceShape.hasTrait(LocalServiceTrait.class)) {
          return serviceShape.expectTrait(LocalServiceTrait.class).getSdkId() + "Client";
      } else {
          throw new UnsupportedOperationException("Non-local services not supported");
      }
  }

  /**
   * Returns the name of the Smithy-generated shim for the provided serviceShape.
   * The serviceShape SHOULD be a localService.
   * ex. example.namespace.ExampleService -> "ExampleServiceShim"
   * @param serviceShape
   * @return
   */
  public static String shimForService(ServiceShape serviceShape) {
    // TODO: Hardcode (ex) Trent -> KMS?
      if (serviceShape.hasTrait(LocalServiceTrait.class)) {
          return serviceShape.expectTrait(LocalServiceTrait.class).getSdkId() + "Shim";
      } else {
          throw new UnsupportedOperationException("Non-local services not supported");
      }
  }

  /**
   * Returns the name of the Python module containing Dafny-generated Python code
   *   from the `types` module from the same Dafny project for the provided Shape.
   * ex. example.namespace.ExampleShape -> "example_namespace_internaldafny_types"
   * @param shapeId
   * @return
   */
  public static String getDafnyPythonTypesModuleNameForShape(ShapeId shapeId) {
    return getDafnyTypesModuleNameForSmithyNamespace(shapeId.getNamespace());
  }

  /**
   * Returns the name of the Python module containing Dafny-generated Python code
   *   from the `types` module from the same Dafny project for the provided smithyNamespace.
   * ex. example.namespace.ExampleShape -> "example_namespace_internaldafny_types"
   * @param smithyNamespace
   * @return
   */
  public static String getDafnyTypesModuleNameForSmithyNamespace(String smithyNamespace) {
    return getDafnyIndexModuleNameForSmithyNamespace(smithyNamespace) + "_types";
  }

  /**
   * Returns the name of the Python module containing Dafny-generated Python code
   *   from the `index` module from the same Dafny project for the provided smithyNamespace.
   * ex. example.namespace.ExampleShape -> "example_namespace_internaldafny"
   * @param smithyNamespace
   * @return
   */
  public static String getDafnyIndexModuleNameForSmithyNamespace(String smithyNamespace) {
    String dafnyExternNamespace = resolveAwsSdkSmithyModelNamespaceToDafnyExternNamespace(smithyNamespace);
    return dafnyExternNamespace.toLowerCase(Locale.ROOT).replace(".", "_") + "_internaldafny";
  }

  public static String resolveAwsSdkSmithyModelNamespaceToDafnyExternNamespace(String smithyNamespace) {
    switch (smithyNamespace) {
      case "com.amazonaws.kms":
        return "software.amazon.cryptography.services.kms";
      case "com.amazonaws.dynamodb":
        return "software.amazon.cryptography.services.dynamodb";
      default:
        throw new IllegalArgumentException("Python codegen for smithyNamespace not supported: " + smithyNamespace);
    }
  }

  /**
   * Imports the Dafny-generated Python type corresponding to the provided shape.
   * ex. example.namespace.ExampleShape -> "from example_namespace_internaldafny_types import DafnyExampleShape"
   * @param shape
   * @return
   */
  private static void importDafnyTypeForAwsSdkShape(PythonWriter writer, Shape shape, GenerationContext context) {
    importDafnyTypeForAwsSdkShape(writer, shape.getId(), context);
  }

  /**
   * Calls writer.addImport to import the corresponding Dafny type
   *   for the provided Smithy ShapeId.
   * This MUST NOT be used to import errors; use `importDafnyTypeForError`.
   * ex. example.namespace.ExampleShape -> "from example_namespace_internaldafny_types import DafnyExampleShape"
   * @param writer
   * @param shapeId
   */
  public static void importDafnyTypeForAwsSdkShape(PythonWriter writer, ShapeId shapeId, GenerationContext context) {
    if (context.model().expectShape(shapeId).hasTrait(ErrorTrait.class)) {
      throw new IllegalArgumentException(
          "Error shapes are not supported in importDafnyTypeForShape. Provided " + shapeId);
    }
    // When generating a Dafny import, must ALWAYS first import module_ to avoid circular dependencies
    writer.addStdlibImport("module_");
    String name = shapeId.getName();
    if (!Utils.isUnitShape(shapeId)) {
      writer.addStdlibImport(getDafnyPythonTypesModuleNameForShape(shapeId),
          name + "_" + name, getDafnyTypeForShape(shapeId));
    }
  }

  /**
   * Returns a String representing the corresponding Dafny type
   *   for the provided shape.
   * This MUST NOT be used for errors; for errors use `getDafnyTypeForError`.
   * ex. example.namespace.ExampleShape -> "DafnyExampleShape"
   * @param shapeId
   * @return
   */
  public static String getDafnyTypeForShape(ShapeId shapeId) {
    if (Utils.isUnitShape(shapeId)) {
      // Dafny models Unit shapes as the Python `None` type
      return "None";
    } else {
      // Catch-all: Return `Dafny[shapeName]`
      return "Dafny" + shapeId.getName();
    }
  }

  /**
   * Returns a String representing the Dafny-generated Python type corresponding to the provided Shape.
   * ex. example.namespace.ExampleShape -> "DafnyExampleShape"
   * @param shape
   * @return
   */
  public static String getDafnyTypeForShape(Shape shape) {
    return getDafnyTypeForShape(shape.getId());
  }

  /**
   * Imports the Dafny-generated Python type corresponding to the provided unionShape.
   * ex. example.namespace.ExampleUnion:IntegerValue -> "from example_namespace_internaldafny_types
   *      import ExampleUnion_IntegerValue"
   * @param unionShape
   * @return
   */
  public static void importDafnyTypeForUnion(PythonWriter writer,
      UnionShape unionShape, MemberShape memberShape) {
    writer.addStdlibImport(
        getDafnyPythonTypesModuleNameForShape(unionShape.getId()),
        getDafnyTypeForUnion(unionShape, memberShape)
    );
  }

  /**
   * Returns a String representing the corresponding Dafny type
   *   for the provided UnionShape and one of its MemberShapes.
   * This MUST ONLY be used for unions and their members; for other shapes use `getDafnyTypeForShape`.
   * ex. example.namespace.ExampleUnion:IntegerValue -> "ExampleUnion_IntegerValue"
   * @param unionShape
   * @param memberShape
   * @return
   */
  public static String getDafnyTypeForUnion(UnionShape unionShape,
      MemberShape memberShape) {
    return unionShape.getId().getName() + "_" + memberShape.getMemberName();
  }
}
