package software.amazon.polymorph.smithypython.customize;

import software.amazon.polymorph.smithypython.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.nameresolver.PythonNameResolver;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.python.codegen.GenerationContext;

public class DafnyImplInterfaceFileWriter implements CustomFileWriter {

  @Override
  public void generateFileForServiceShape(
      ServiceShape serviceShape, GenerationContext codegenContext) {
    String moduleName = codegenContext.settings().getModuleName();
    String clientName = PythonNameResolver.clientForService(serviceShape);
    String implModulePrelude = DafnyNameResolver.getDafnyImplModuleNamespaceForShape(serviceShape);

    // TODO: StringBuilder
    String operations = "";
    for (OperationShape operationShape : codegenContext.model().getOperationShapes()) {
      operations += """
          "%1$s": self.%2$s.%1$s,\n
          """.formatted(operationShape.getId().getName(), "impl");
    }
    String allOperations = operations;

    // TODO: refactor to DafnyImplInterfaceFileWriter
    // TODO: Naming of this file?
    codegenContext.writerDelegator()
        .useFileWriter(moduleName + "/dafnyImplInterface.py", "", writer -> {
          writer.write(
              """
                  from $L import $L
                            
                  class DafnyImplInterface:
                      $L: $L | None = None
                            
                      def handle_request(self, input):
                      
                          # TODO: populate map at runtime (since impl is only populated at runtime, and avoids a None exception),
                          #       but don't re-populate it at every handle_request call, i.e. cache
                          operation_map = {
                              $L
                          }
                            
                          operation_name = input[0]
                          if input[1] == None:
                              return operation_map[operation_name]()
                          else:
                              return operation_map[operation_name](input[1])
                  """, implModulePrelude, clientName, "impl", clientName, allOperations
          );
        });
  }
}
