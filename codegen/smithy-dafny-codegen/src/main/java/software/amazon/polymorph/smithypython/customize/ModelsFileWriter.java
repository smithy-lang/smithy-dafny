package software.amazon.polymorph.smithypython.customize;

import software.amazon.polymorph.smithypython.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.StructureShape;
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

    final LocalServiceTrait localServiceTrait = serviceShape.expectTrait(LocalServiceTrait.class);
    final StructureShape configShape = codegenContext.model().expectShape(localServiceTrait.getConfigId(), StructureShape.class);
    System.out.println(configShape.getAllMembers());


    /*
        blob_value: Any
        boolean_value: Any
        string_value: Any
        integer_value: Any
        long_value: Any

        def __init__(self, blob_value, boolean_value, string_value, integer_value, long_value):
            self.long_value = long_value
            self.blob_value = blob_value
            self.boolean_value = boolean_value
            self.string_value = string_value
            self.integer_value = integer_value
     */

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
