package software.amazon.polymorph.smithypython.customize;

import java.util.HashSet;
import java.util.Set;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.python.codegen.GenerationContext;

public class TempConversionLibFileWriter implements CustomFileWriter {

  @Override
  public void generateFileForServiceShape(
      ServiceShape serviceShape, GenerationContext codegenContext) {
    String moduleName = codegenContext.settings().getModuleName();

    codegenContext.writerDelegator().useFileWriter(moduleName + "/temp_conversion_lib.py", "", writer -> {
      writer.write(
          """
              from _dafny import (
                  Seq,
                  Map
              )
              
              # TODO: Move to DafnyConversionLibrary
              class ToDafnyConversionLibrary:
                  def GenericToList(dafnyValues: Seq, converter):
                      return_list = []
                      
              """
      );
    });
  }

}
