package software.amazon.polymorph.smithypython.customize;

import software.amazon.polymorph.smithypython.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.nameresolver.PythonNameResolver;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.python.codegen.GenerationContext;

public class DafnyProtocolFileWriter implements CustomFileWriter {

  @Override
  public void generateFileForServiceShape(
      ServiceShape serviceShape, GenerationContext codegenContext) {
    String moduleName = codegenContext.settings().getModuleName();
    // I'm not sure how we use this.. maybe for better type checking?
    // maybe something like DafnyInput = Union[forall operations: DafnyName(operation)]
    codegenContext.writerDelegator().useFileWriter(moduleName + "/dafny_protocol.py", "", writer -> {
      writer.write(
          """
          class DafnyRequest:
              # TODO: smithy-python requires some class for the "application protocol input",
              # but we do not use this at this time.
              pass
              
          class DafnyResponse:
              # TODO: smithy-python requires some class for the "application protocol output",
              # but we do not use this at this time.
              pass
          """
      );
    });
  }

}
