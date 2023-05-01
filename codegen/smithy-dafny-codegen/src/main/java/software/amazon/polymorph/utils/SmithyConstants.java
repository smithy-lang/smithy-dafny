package software.amazon.polymorph.utils;

import java.util.Set;

import software.amazon.smithy.model.shapes.ShapeType;

public class SmithyConstants {
    public static final Set<ShapeType> LIST_MAP_SET_SHAPE_TYPES;
    static {
        LIST_MAP_SET_SHAPE_TYPES = Set.of(
          ShapeType.LIST, ShapeType.SET, ShapeType.MAP
        );
    }
}
