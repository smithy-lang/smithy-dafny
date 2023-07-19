package software.amazon.polymorph.smithypython.customize;

import software.amazon.polymorph.smithypython.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.nameresolver.SmithyNameResolver;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/**
 * Creates a dafnyImplInterface.py file containing a DafnyImplInterface class.
 * This provides a static (meaning "unchanging") interface for the
 * Smithy-Python-generated client.py request handler to interact with.
 *
 * (We do this because we cannot extensively customize this part of client.py code generation.
 *  Instead, we plug this interface into the part we can customize,
 *  and do the rest of the customization in a file we control (this file).)
 */
public class DafnyImplInterfaceFileWriter implements CustomFileWriter {

  @Override
  public void generateFileForServiceShape(
      ServiceShape serviceShape, GenerationContext codegenContext) {
    String moduleName = codegenContext.settings().getModuleName();
    String clientName = SmithyNameResolver.clientForService(serviceShape);
    String implModulePrelude = DafnyNameResolver.getDafnyImplModuleNamespaceForShape(serviceShape);

    codegenContext.writerDelegator()
      .useFileWriter(moduleName + "/dafnyImplInterface.py", "", writer -> {
        writer.write(
            """
                from $L import $L
                from .dafny_protocol import DafnyRequest
                          
                class DafnyImplInterface:
                    $L: $L | None = None
                    
                    # operation_map cannot be created at dafnyImplInterface create time,
                    # as the map's values reference values inside `self.impl`,
                    # and impl is only populated at runtime.
                    # Accessing these before impl is populated results in an error.
                    # At runtime, the map is populated once and cached.
                    operation_map = None
                          
                    def handle_request(self, input: DafnyRequest):
                        if self.operation_map is None:
                            self.operation_map = {
                                ${C|}
                            }
                          
                         # This logic is where a typical Smithy client would expect the "server" to be.
                         # This code can be thought of as logic our Dafny "server" uses
                         #   to route incoming client requests to the correct request handler code.
                        if input.dafny_operation_input is None:
                            return self.operation_map[input.operation_name]()
                        else:
                            return self.operation_map[input.operation_name](input.dafny_operation_input)
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
