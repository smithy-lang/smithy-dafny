package software.amazon.polymorph.smithypython.customize;

import java.util.Set;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.python.codegen.GenerationContext;

public interface CustomFileWriter {
  default void customizeFileForServiceShape(ServiceShape serviceShape, GenerationContext codegenContext) { }
  default void customizeFileForNonServiceOperationShapes(Set<ShapeId> operationShapeIds, GenerationContext codegenContext) { }
}
