package software.amazon.polymorph.smithygo;

import software.amazon.smithy.codegen.core.WriterDelegator;
import software.amazon.smithy.model.shapes.Shape;

public interface ShapeGenerator<T extends Shape> {
    public void generate(T shape);
}
