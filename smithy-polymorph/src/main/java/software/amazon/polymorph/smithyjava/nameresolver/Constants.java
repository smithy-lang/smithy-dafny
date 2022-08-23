package software.amazon.polymorph.smithyjava.nameresolver;

import com.squareup.javapoet.ClassName;

import java.util.Set;

import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ShapeType;

public class Constants {
    public static ShapeId SMITHY_API_UNIT = ShapeId.fromParts("smithy.api", "Unit");
    public static ClassName DAFNY_RESULT_CLASS_NAME = ClassName.get("Wrappers_Compile", "Result");
    public static ClassName DAFNY_TUPLE0_CLASS_NAME = ClassName.get("dafny", "Tuple0");
    public static Set<ShapeType> SHAPE_TYPES_LIST_MAP_SET = Set.of(ShapeType.LIST, ShapeType.MAP, ShapeType.SET);
}
