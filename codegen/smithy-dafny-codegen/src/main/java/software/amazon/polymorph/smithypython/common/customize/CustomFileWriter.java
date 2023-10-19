package software.amazon.polymorph.smithypython.common.customize;

import java.util.Set;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.python.codegen.GenerationContext;

/**
 * Interface for writing custom Dafny-Python code to files.
 */
public interface CustomFileWriter {

  /**
   * Writes code specific to the file targeted by the CustomFileWriter for the provided ServiceShape.
   * The ServiceShape SHOULD be a shape annotated with the `aws.polymorph#localService` trait.
   * @param serviceShape
   * @param codegenContext
   */
  default void customizeFileForServiceShape(ServiceShape serviceShape, GenerationContext codegenContext) { }

  /**
   * Given the provided operationShapeIds, write code specific to the file targeted by the CustomFileWriter.
   * The operationShapeIds MUST NOT be attached to a ServiceShape that was passed to this file in
   *   a call to `customizeFileForServiceShape`.
   * This function will generate code for operations that are NOT attached to a localService.
   * @param operationShapeIds
   * @param codegenContext
   */
  default void customizeFileForNonServiceOperationShapes(Set<ShapeId> operationShapeIds, GenerationContext codegenContext) { }
}
