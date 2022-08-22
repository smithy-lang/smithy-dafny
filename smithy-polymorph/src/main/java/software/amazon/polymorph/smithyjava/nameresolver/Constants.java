package software.amazon.polymorph.smithyjava.nameresolver;

import com.squareup.javapoet.ClassName;

import software.amazon.smithy.model.shapes.ShapeId;

public class Constants {
    public static ShapeId SMITHY_API_UNIT = ShapeId.fromParts("smithy.api", "Unit");
    public static ClassName DAFNY_RESULT_CLASS_NAME = ClassName.get("Wrappers_Compile", "Result");
    public static ClassName DAFNY_TUPLE0_CLASS_NAME = ClassName.get("dafny", "Tuple0");
}
