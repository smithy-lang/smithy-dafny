package software.amazon.polymorph.smithypython.nameresolver;

import java.util.Locale;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.python.codegen.PythonWriter;

/**
 * Contains utility functions that map Smithy shapes
 * to useful Dafny strings.
 */
public class DafnyNameResolver {

  /**
   * Returns the name of the Python module containing Dafny-generated Python code
   *   from the `types` module from the same Dafny project for the provided Shape.
   * @param shape
   * @return
   */
  public static String getDafnyPythonTypesModuleNameForShape(Shape shape) {
    return getDafnyPythonTypesModuleNameForShape(shape.getId());
  }

  /**
   * Returns the name of the Python module containing Dafny-generated Python code
   *   from the `types` module from the same Dafny project for the provided Shape.
   * @param shapeId
   * @return
   */
  public static String getDafnyPythonTypesModuleNameForShape(ShapeId shapeId) {
    return getDafnyTypesModuleNameForSmithyNamespace(shapeId.getNamespace());
  }

  /**
   * Returns the name of the Python module containing Dafny-generated Python code
   *   from the `index` module from the same Dafny project for the provided Shape.
   * @param shape
   * @return
   */
  public static String getDafnyPythonIndexModuleNameForShape(Shape shape) {
    return getDafnyPythonIndexModuleNameForShape(shape.getId());
  }

  /**
   * Returns the name of the Python module containing Dafny-generated Python code
   *   from the `index` module from the same Dafny project for the provided Shape.
   * @param shapeId
   * @return
   */
  public static String getDafnyPythonIndexModuleNameForShape(ShapeId shapeId) {
    return getDafnyIndexModuleNameForSmithyNamespace(shapeId.getNamespace());
  }

  /**
   * Returns the name of the Python module containing Dafny-generated Python code
   *   from the `index` module from the same Dafny project for the provided smithyNamespace.
   * @param smithyNamespace
   * @return
   */
  public static String getDafnyIndexModuleNameForSmithyNamespace(String smithyNamespace) {
    return smithyNamespace.toLowerCase(Locale.ROOT).replace(".", "_") + "_internaldafny";
  }

  /**
   * Returns the name of the Python module containing Dafny-generated Python code
   *   from the `types` module from the same Dafny project for the provided smithyNamespace.
   * @param smithyNamespace
   * @return
   */
  public static String getDafnyTypesModuleNameForSmithyNamespace(String smithyNamespace) {
    return getDafnyIndexModuleNameForSmithyNamespace(smithyNamespace) + "_types";
  }

  /**
   * Returns a String representing the corresponding Dafny type
   *   for the provided shape.
   * This MUST NOT be used for errors; for errors use `getDafnyTypeForError`.
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
   * @param shape
   * @return
   */
  public static String getDafnyTypeForShape(Shape shape) {
    return getDafnyTypeForShape(shape.getId());
  }

  /**
   * Imports the Dafny-generated Python type corresponding to the provided shape.
   * @param shape
   * @return
   */
  private static void importDafnyTypeForShape(PythonWriter writer, Shape shape) {
    importDafnyTypeForShape(writer, shape.getId());
  }

  /**
   * Calls writer.addImport to import the corresponding Dafny type
   *   for the provided Smithy ShapeId.
   * This MUST NOT be used to import errors; use `importDafnyTypeForError`.
   * @param writer
   * @param shapeId
   */
  public static void importDafnyTypeForShape(PythonWriter writer, ShapeId shapeId) {
    // When generating a Dafny import, must ALWAYS first import module_ to avoid circular dependencies
    writer.addStdlibImport("module_");
    String name = shapeId.getName();
    if (!Utils.isUnitShape(shapeId)) {
      writer.addStdlibImport(getDafnyPythonTypesModuleNameForShape(shapeId),
          name + "_" + name, getDafnyTypeForShape(shapeId));
    }
  }

  /**
   * Returns a String representing the client interface type for the provided serviceShape
   *   as Dafny models the interface type.
   * @param serviceShape
   * @return
   */
  public static String getDafnyClientInterfaceTypeForServiceShape(ServiceShape serviceShape) {
    return "I" + serviceShape.getId().getName() + "Client";
  }

  /**
   * Returns a String representing the client interface type for the provided serviceShape
   *   as Dafny models the interface type.
   * @param serviceShape
   * @return
   */
  public static String getDafnyClientTypeForServiceShape(ServiceShape serviceShape) {
    return serviceShape.getId().getName() + "Client";
  }

  /**
   * Returns a String representing the interface type for the provided resourceShape
   *   as Dafny models the interface type.
   * @param resourceShape
   * @return
   */
  public static String getDafnyInterfaceTypeForResourceShape(ResourceShape resourceShape) {
    return "I" + resourceShape.getId().getName();
  }

  /**
   * Imports the Dafny-generated Python type corresponding to the provided resourceShape.
   * @param resourceShape
   * @return
   */
  public static void importDafnyTypeForResourceShape(PythonWriter writer, ResourceShape resourceShape) {
    // When generating a Dafny import, must ALWAYS first import module_ to avoid circular dependencies
    writer.addStdlibImport("module_");
    writer.addStdlibImport(
        getDafnyPythonTypesModuleNameForShape(resourceShape.getId()),
        getDafnyInterfaceTypeForResourceShape(resourceShape)
    );
  }

  /**
   * Imports the Dafny-generated Python type corresponding to the provided serviceShape.
   * @param serviceShape
   * @return
   */
  public static void importDafnyTypeForServiceShape(PythonWriter writer, ServiceShape serviceShape) {
    // When generating a Dafny import, must ALWAYS first import module_ to avoid circular dependencies
    writer.addStdlibImport("module_");
    writer.addStdlibImport(
        getDafnyPythonTypesModuleNameForShape(serviceShape.getId()),
        getDafnyClientInterfaceTypeForServiceShape(serviceShape)
    );
  }

  /**
   * Returns a String representing the corresponding Dafny type
   *   for the provided Error shape.
   * This MUST ONLY be used for errors; for other shapes use `getDafnyTypeForShape`.
   * @param shape
   * @return
   */
  public static String getDafnyTypeForError(Shape shape) {
    return getDafnyTypeForError(shape.getId());
  }

  /**
   * Returns a String representing the Dafny-generated Python type corresponding to the provided error shape.
   * @param shapeId
   * @return
   */
  public static String getDafnyTypeForError(ShapeId shapeId) {
    return "Error_" + shapeId.getName();
  }

  /**
   * Returns a String representing the corresponding Dafny type
   *   for the provided UnionShape and one of its MemberShapes.
   * This MUST ONLY be used for unions and their members; for other shapes use `getDafnyTypeForShape`.
   * @param unionShape
   * @param memberShape
   * @return
   */
  public static String getDafnyTypeForUnion(UnionShape unionShape,
      MemberShape memberShape) {
    return unionShape.getId().getName() + "_" + memberShape.getMemberName();
  }

  /**
   * Imports the Dafny-generated Python type corresponding to the provided unionShape.
   * @param unionShape
   * @return
   */
  public static void importDafnyTypeForUnion(PythonWriter writer,
      UnionShape unionShape, MemberShape memberShape) {
    writer.addStdlibImport(
        getDafnyPythonTypesModuleNameForShape(unionShape),
        getDafnyTypeForUnion(unionShape, memberShape)
    );
  }

  /**
   * Calls writer.addImport to import the corresponding Dafny type
   *   for the provided Smithy ShapeId.
   * This MUST ONLY be used for errors; for other shapes use `importDafnyTypeForShape`.
   * @param writer
   * @param shapeId
   */
  public static void importDafnyTypeForError(PythonWriter writer, ShapeId shapeId) {
    // When generating a Dafny import, must ALWAYS first import module_ to avoid circular dependencies
    writer.addStdlibImport("module_");
    writer.addStdlibImport(getDafnyPythonTypesModuleNameForShape(shapeId),
      getDafnyTypeForError(shapeId));
  }

  /**
   * Imports the generic Dafny error type for the provided namespace.
   * @param writer
   * @param namespace
   */
  public static void importGenericDafnyErrorTypeForNamespace(PythonWriter writer, String namespace) {
    // When generating a Dafny import, must ALWAYS first import module_ to avoid circular dependencies
    writer.addStdlibImport("module_");
    writer.addStdlibImport(getDafnyTypesModuleNameForSmithyNamespace(namespace), "Error");
  }
}
