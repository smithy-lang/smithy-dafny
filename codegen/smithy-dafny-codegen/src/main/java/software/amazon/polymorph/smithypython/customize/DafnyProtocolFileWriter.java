package software.amazon.polymorph.smithypython.customize;

import java.util.HashSet;
import java.util.Set;
import software.amazon.polymorph.smithypython.nameresolver.DafnyNameResolver;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/**
 * Writes the dafny_protocol.py file.
 */
public class DafnyProtocolFileWriter implements CustomFileWriter {

  @Override
  public void generateFileForServiceShape(
      ServiceShape serviceShape, GenerationContext codegenContext) {
    String moduleName = codegenContext.settings().getModuleName();

    Set<ShapeId> inputShapeIds = new HashSet<>();
    Set<ShapeId> outputShapeIds = new HashSet<>();

    for (ShapeId operationShapeId : serviceShape.getAllOperations()) {
      OperationShape operationShape = codegenContext.model()
          .expectShape(operationShapeId, OperationShape.class);

      inputShapeIds.add(operationShape.getInputShape());
      outputShapeIds.add(operationShape.getOutputShape());
    }

    codegenContext.writerDelegator().useFileWriter(moduleName + "/dafny_protocol.py", "", writer -> {
      writer.write(
          """
              import Wrappers
              from typing import Union
                        
              class DafnyRequest:
                  operation_name: str
                  dafny_operation_input: Union[
                      ${C|}
                  ]
                  
                  def __init__(self, operation_name, dafny_operation_input):
                      self.operation_name = operation_name
                      self.dafny_operation_input = dafny_operation_input
                  
              class DafnyResponse(Wrappers.Result):
                  def __init__(self):
                      super.__init__(self)
              """,
          writer.consumer(w -> generateDafnyOperationInputUnionValues(inputShapeIds, w))
      );
    });
  }

  private void generateDafnyOperationInputUnionValues(
      Set<ShapeId> inputShapeIds, PythonWriter writer) {
    for (ShapeId inputShapeId : inputShapeIds) {
      DafnyNameResolver.importDafnyTypeForShape(writer, inputShapeId);
      writer.write("$L,", DafnyNameResolver.getDafnyTypeForShape(inputShapeId));
    }
  }

}
