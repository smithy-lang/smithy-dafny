// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.common.nameresolver;

import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;

/**
 * Utils class containing NameResolver utility functions. This should contain helper methods common
 * to >1 name resolver. TODO-Python: Once Utils class has a more clearly defined scope, refactor
 * such that it is not a generic Utils class
 */
public class Utils {

  /**
   * Returns true if `shapeId` is a Smithy Unit shape.
   *
   * @param shapeId
   * @return
   */
  public static boolean isUnitShape(ShapeId shapeId) {
    return shapeId.getNamespace().equals("smithy.api") && shapeId.getName().equals("Unit");
  }

  private static boolean isUnitShape(Shape shape) {
    return isUnitShape(shape.getId());
  }
}
