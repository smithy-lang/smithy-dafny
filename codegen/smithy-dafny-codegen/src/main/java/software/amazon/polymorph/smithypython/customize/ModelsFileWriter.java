package software.amazon.polymorph.smithypython.customize;

import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.python.codegen.GenerationContext;


/**
 * Extends the Smithy-Python-generated models.py file
 * by adding Dafny plugin models.
 */
public class ModelsFileWriter implements CustomFileWriter {
  @Override
  public void generateFileForServiceShape(
      ServiceShape serviceShape, GenerationContext codegenContext) {
    String moduleName = codegenContext.settings().getModuleName();

    // TODO: Ideally I don't need to do this, but this almost seems necessary
    // to avoid having to fork Smithy-Python...
    codegenContext.writerDelegator().useFileWriter(moduleName + "/models.py", "", writer -> {
      writer.write(
          """
             class Unit:
                 pass
              """
      );
    });
  }

}
