package software.amazon.polymorph.smithyjava.modeled;

import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.TypeName;
import software.amazon.polymorph.smithyjava.generator.ToNative;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.smithy.model.node.ObjectNode;
import software.amazon.smithy.model.shapes.Shape;

public class ModeledNode {

    public CodeBlock modeledNode(JavaLibrary subject, Shape shape, String variableName, ObjectNode node) {
        CodeBlock code = new CodeBlock();
        TypeName typeName = subject.nativeNameResolver.typeForShape(shape.toShapeId());
        ToNative.createNativeBuilder();
    }
}
