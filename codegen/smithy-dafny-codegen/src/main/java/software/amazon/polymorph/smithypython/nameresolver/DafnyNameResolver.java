package software.amazon.polymorph.smithypython.nameresolver;

import java.util.Locale;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.python.codegen.PythonWriter;

/**
 * Contains utility functions that map Smithy shapes
 * to useful Dafny strings.
 */
public class DafnyNameResolver {

  private static String getDafnyTypesModuleNamespaceForShape(Shape shape) {
    return getDafnyTypesModuleNamespaceForShape(shape.getId());
  }

  public static String getDafnyTypesModuleNamespaceForShape(ShapeId shapeId) {
    return getDafnyTypesModuleNamespaceForSmithyNamespace(shapeId.getNamespace());
  }

  public static String getDafnyIndexModuleNamespaceForShape(Shape shape) {
    return getDafnyIndexModuleNamespaceForShape(shape.getId());
  }

  public static String getDafnyIndexModuleNamespaceForShape(ShapeId shapeId) {
    return getDafnyIndexModuleNamespaceForSmithyNamespace(shapeId.getNamespace());
  }

  public static String getDafnyIndexModuleNamespaceForSmithyNamespace(String smithyNamespace) {
    return smithyNamespace.toLowerCase(Locale.ROOT).replace(".", "_") + "_internaldafny";
  }

  public static String getDafnyTypesModuleNamespaceForSmithyNamespace(String smithyNamespace) {
    return getDafnyIndexModuleNamespaceForSmithyNamespace(smithyNamespace) + "_types";
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

  public static String getDafnyTypeForShape(Shape shape) {
    return getDafnyTypeForShape(shape.getId());
  }

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
      writer.addStdlibImport(getDafnyTypesModuleNamespaceForShape(shapeId),
          name + "_" + name, getDafnyTypeForShape(shapeId));
    }
  }

  /**
   * Returns a String representing the client interface type for the provided serviceShape.
   * @param serviceShape
   * @return
   */
  public static String getDafnyClientInterfaceTypeForServiceShape(ServiceShape serviceShape) {
    return "I" + serviceShape.getId().getName() + "Client";
  }

  /**
   * Returns a String representing the interface type for the provided resourceShape.
   * @param resourceShape
   * @return
   */
  public static String getDafnyClientInterfaceTypeForResourceShape(ResourceShape resourceShape) {
    return "I" + resourceShape.getId().getName();
  }

  public static void importDafnyTypeForResourceShape(PythonWriter writer, ResourceShape resourceShape) {
    // When generating a Dafny import, must ALWAYS first import module_ to avoid circular dependencies
    writer.addStdlibImport("module_");
    writer.addStdlibImport(
        getDafnyTypesModuleNamespaceForShape(resourceShape.getId()),
        getDafnyClientInterfaceTypeForResourceShape(resourceShape)
    );
  }

  public static void importDafnyTypeForServiceShape(PythonWriter writer, ServiceShape serviceShape) {
    // When generating a Dafny import, must ALWAYS first import module_ to avoid circular dependencies
    writer.addStdlibImport("module_");
    writer.addStdlibImport(
        getDafnyTypesModuleNamespaceForShape(serviceShape.getId()),
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

  public static String getDafnyTypeForError(ShapeId shapeId) {
    return "Error_" + shapeId.getName();
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
    writer.addStdlibImport(getDafnyTypesModuleNamespaceForShape(shapeId),
      getDafnyTypeForError(shapeId));
  }

  public static void importGenericDafnyErrorTypeForNamespace(PythonWriter writer, String namespace) {
    // When generating a Dafny import, must ALWAYS first import module_ to avoid circular dependencies
    writer.addStdlibImport("module_");
    writer.addStdlibImport(getDafnyTypesModuleNamespaceForSmithyNamespace(namespace), "Error");
  }
}
