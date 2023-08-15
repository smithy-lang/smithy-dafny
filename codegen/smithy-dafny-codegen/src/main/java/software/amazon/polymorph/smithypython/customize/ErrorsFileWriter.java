package software.amazon.polymorph.smithypython.customize;

import java.util.TreeSet;
import java.util.stream.Collectors;
import software.amazon.smithy.codegen.core.CodegenContext;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.python.codegen.CodegenUtils;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/**
 * Extends the Smithy-Python-generated errors.py file
 * by adding Dafny plugin errors.
 */
public class ErrorsFileWriter implements CustomFileWriter {

  @Override
  public void generateFileForServiceShape(
      ServiceShape serviceShape, GenerationContext codegenContext) {
    String moduleName = codegenContext.settings().getModuleName();

    codegenContext.writerDelegator().useFileWriter(moduleName + "/errors.py", "", writer -> {
      writer.addStdlibImport("typing", "Dict");
      writer.addStdlibImport("typing", "Any");

      var deserializingErrorShapes = new TreeSet<StructureShape>(
          codegenContext.model().getStructureShapesWithTrait(ErrorTrait.class)
              .stream()
              .filter(structureShape -> structureShape.getId().getNamespace()
                  .equals(codegenContext.settings().getService().getNamespace()))
              .collect(Collectors.toSet()));

      for (StructureShape errorShape : deserializingErrorShapes) {
        renderError(codegenContext, writer, errorShape);
      }

      writer.write(
          """
             class CollectionOfErrors(ApiError[Literal["CollectionOfErrors"]]):
                 code: Literal["CollectionOfErrors"] = "CollectionOfErrors"
                 message: str
                 # TODO: To add `list` here, I'd need a typehint... what should the object type be?
                 def __init__(
                     self,
                     *,
                     message: str,
                     list
                 ):
                     super().__init__(message)
                     self.list = list
                             
                 def as_dict(self) -> Dict[str, Any]:
                     ""\"Converts the CollectionOfErrors to a dictionary.
                             
                     The dictionary uses the modeled shape names rather than the parameter names as
                     keys to be mostly compatible with boto3.
                     ""\"
                     return {
                         'message': self.message,
                         'code': self.code,
                         'list': self.list,
                     }
                             
                 @staticmethod
                 def from_dict(d: Dict[str, Any]) -> "CollectionOfErrors":
                     ""\"Creates a CollectionOfErrors from a dictionary.
                             
                     The dictionary is expected to use the modeled shape names rather than the
                     parameter names as keys to be mostly compatible with boto3.
                     ""\"
                     kwargs: Dict[str, Any] = {
                         'message': d['message'],
                         'list': d['list']
                     }
                             
                     return CollectionOfErrors(**kwargs)
                             
                 def __repr__(self) -> str:
                     result = "CollectionOfErrors("
                     result += f'message={self.message},'
                     if self.message is not None:
                         result += f"message={repr(self.message)}"
                     result += f'list={self.list}'
                     result += ")"
                     return result
                             
                 def __eq__(self, other: Any) -> bool:
                     if not isinstance(other, CollectionOfErrors):
                         return False
                     if not (self.list == other.list):
                         return False
                     attributes: list[str] = ['message','message']
                     return all(
                         getattr(self, a) == getattr(other, a)
                         for a in attributes
                     )
                             
             # TODO: Should this extend ApiError...?
             # Probably not... as this doesn't have a message attribute...
             class OpaqueError(ApiError[Literal["OpaqueError"]]):
                 code: Literal["OpaqueError"] = "OpaqueError"
                 # TODO: The type of obj is only known at runtime, and therefore should *probably* should not have a typehint
                 # Probably no-op here, but we should think more deeply about this...
                 def __init__(
                     self,
                     *,
                     obj
                 ):
                     # TODO: Remove superclass construction if we decide this shouldn't extend ApiError
                     super().__init__("")
                     self.obj = obj
                             
                 def as_dict(self) -> Dict[str, Any]:
                     ""\"Converts the OpaqueError to a dictionary.
                             
                     The dictionary uses the modeled shape names rather than the parameter names as
                     keys to be mostly compatible with boto3.
                     ""\"
                     return {
                         'message': self.message,
                         'code': self.code,
                         'obj': self.obj,
                     }
                             
                 @staticmethod
                 def from_dict(d: Dict[str, Any]) -> "OpaqueError":
                     ""\"Creates a OpaqueError from a dictionary.
                             
                     The dictionary is expected to use the modeled shape names rather than the
                     parameter names as keys to be mostly compatible with boto3.
                     ""\"
                     kwargs: Dict[str, Any] = {
                         'message': d['message'],
                         'obj': d['obj']
                     }
                             
                     return OpaqueError(**kwargs)
                             
                 def __repr__(self) -> str:
                     result = "OpaqueError("
                     result += f'message={self.message},'
                     if self.message is not None:
                         result += f"message={repr(self.message)}"
                     result += f'obj={self.obj}'
                     result += ")"
                     return result
                             
                 def __eq__(self, other: Any) -> bool:
                     if not isinstance(other, OpaqueError):
                         return False
                     if not (self.obj == other.obj):
                         return False
                     attributes: list[str] = ['message','message']
                     return all(
                         getattr(self, a) == getattr(other, a)
                         for a in attributes
                     )
              """
      );
    });

  }

  // This is lifted from Smithy-Python, where it is not sufficiently customizable
  // to be used for Resource error generation.
  // TODO: Reconcile this with Smithy-Python
  private void renderError(GenerationContext context, PythonWriter writer, StructureShape shape) {
    writer.addStdlibImport("typing", "Dict");
    writer.addStdlibImport("typing", "Any");
    writer.addStdlibImport("typing", "Literal");

    var code = shape.getId().getName();
    var symbol = context.symbolProvider().toSymbol(shape);
    var apiError = CodegenUtils.getApiError(context.settings());
    writer.openBlock("class $L($T[Literal[$S]]):", "", symbol.getName(), apiError, code, () -> {
      writer.write("code: Literal[$1S] = $1S", code);
      writer.write("message: str");
    });
    writer.write("");
  }

}
