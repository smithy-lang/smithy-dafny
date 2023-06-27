package software.amazon.polymorph.utils;

import java.util.Set;

import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ShapeType;

public class SmithyConstants {
    public static final Set<ShapeType> LIST_MAP_SET_SHAPE_TYPES;
    public static final String SMITHY_API_NAMESPACE = "smithy.api";
    public static final ShapeId SMITHY_STRING_SHAPE_ID = ShapeId.fromParts(SMITHY_API_NAMESPACE, "String");
    public static final ShapeId SMITHY_UNIT_SHAPE_ID = ShapeId.fromParts(SMITHY_API_NAMESPACE, "Unit");

    static {
        LIST_MAP_SET_SHAPE_TYPES = Set.of(
          ShapeType.LIST, ShapeType.SET, ShapeType.MAP
        );
    }
}
