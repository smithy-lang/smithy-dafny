package software.amazon.polymorph.smithypython.nameresolver;

import java.util.Locale;
import software.amazon.polymorph.smithypython.DafnyProtocolGenerator;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.python.codegen.PythonWriter;

public class DafnyNameResolver {

  private static String getDafnyTypesModuleNamespaceForShape(Shape shape) {
    return getDafnyTypesModuleNamespaceForShape(shape.getId());
  }

  public static String getDafnyTypesModuleNamespaceForShape(ShapeId shapeId) {
    return shapeId.getNamespace().toLowerCase(Locale.ROOT) + ".internaldafny.types";
  }

  public static String getDafnyImplModuleNamespaceForShape(Shape shape) {
    return getDafnyImplModuleNamespaceForShape(shape.getId());
  }

  public static String getDafnyImplModuleNamespaceForShape(ShapeId shapeId) {
    return shapeId.getNamespace().toLowerCase(Locale.ROOT) + ".internaldafny.impl";
  }

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
    String name = shapeId.getName();
    if (!Utils.isUnitShape(shapeId)) {
      writer.addImport(getDafnyTypesModuleNamespaceForShape(shapeId),
          name + "_" + name, getDafnyTypeForShape(shapeId));
    }
  }

  /**
   * Calls writer.addImport to import the corresponding Dafny type
   *   for the provided Smithy ShapeId.
   * This MUST ONLY be used for errors; for other shapes use `importDafnyTypeForShape`.
   * @param writer
   * @param shapeId
   */
  public static void importDafnyTypeForError(PythonWriter writer, ShapeId shapeId) {
    String name = shapeId.getName();
    writer.addImport(getDafnyTypesModuleNamespaceForShape(shapeId),
      "Error_" + name);
  }
}
