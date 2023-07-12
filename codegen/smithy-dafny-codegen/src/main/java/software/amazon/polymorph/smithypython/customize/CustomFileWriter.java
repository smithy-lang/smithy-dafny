package software.amazon.polymorph.smithypython.customize;

import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.python.codegen.GenerationContext;

public interface CustomFileWriter {

  public static void generateFile(ServiceShape serviceShape, GenerationContext codegenContext) { }

}
