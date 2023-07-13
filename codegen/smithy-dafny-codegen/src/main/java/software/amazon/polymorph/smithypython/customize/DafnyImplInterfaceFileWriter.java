package software.amazon.polymorph.smithypython.customize;

import software.amazon.polymorph.smithypython.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.nameresolver.PythonNameResolver;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

public class DafnyImplInterfaceFileWriter implements CustomFileWriter {

  @Override
  public void generateFileForServiceShape(
      ServiceShape serviceShape, GenerationContext codegenContext) {
    String moduleName = codegenContext.settings().getModuleName();
    String clientName = PythonNameResolver.clientForService(serviceShape);
    String implModulePrelude = DafnyNameResolver.getDafnyImplModuleNamespaceForShape(serviceShape);

    codegenContext.writerDelegator()
      .useFileWriter(moduleName + "/dafnyImplInterface.py", "", writer -> {
        writer.write(
            """
                from $L import $L
                          
                class DafnyImplInterface:
                    $L: $L | None = None
                    
                    # operation_map cannot be created at dafnyImplInterface create time,
                    # as the map's values reference values inside `self.impl`,
                    # and impl is only populated at runtime.
                    # Accessing these before impl is populated results in an error.
                    # At runtime, the map is populated once and cached.
                    operation_map = None
                          
                    def handle_request(self, input):
                        if self.operation_map == None:
                            self.operation_map = {
                                ${C|}
                            }
                          
                         # `input` stores the following:
                         # - input[0] = operation name
                         # - input[1] = Dafny-modelled operation input ("serialized")
                         # This logic is where a typical Smithy client would expect the "server" to be.
                         # This code can be thought of as logic our Dafny "server" uses
                         #   to route incoming client requests to the correct request handler code.
                        operation_name = input[0]
                        if input[1] == None:
                            return self.operation_map[operation_name]()
                        else:
                            return self.operation_map[operation_name](input[1])
                """, implModulePrelude, clientName, "impl", clientName,
            writer.consumer(w -> generateImplInterfaceOperationMap(codegenContext, w)));
      });
  }

  private void generateImplInterfaceOperationMap(
      GenerationContext codegenContext, PythonWriter writer) {
    for (OperationShape operationShape : codegenContext.model().getOperationShapes()) {
      writer.write("""
          "$L": self.$L.$L,""",
          operationShape.getId().getName(), "impl", operationShape.getId().getName());
    }
  }
}
