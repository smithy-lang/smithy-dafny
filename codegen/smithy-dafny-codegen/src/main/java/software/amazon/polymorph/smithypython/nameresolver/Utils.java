package software.amazon.polymorph.smithypython.nameresolver;

import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;

public class Utils {

  public static boolean isUnitShape(ShapeId shapeId) {
  return shapeId.getNamespace().equals("smithy.api")
      && shapeId.getName().equals("Unit");
}

  /**
   * Returns a String representing the name of the Dafny type for the provided shape.
   * @param shape
   * @return
   */

  private static boolean isUnitShape(Shape shape) {
    return isUnitShape(shape.getId());
  }
  // TODO: Once Utils class has a more clearly defined scope,
  // refactor such that it is not a generic Utils class


}
