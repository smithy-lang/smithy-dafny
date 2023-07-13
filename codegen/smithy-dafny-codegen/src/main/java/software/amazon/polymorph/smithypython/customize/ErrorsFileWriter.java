package software.amazon.polymorph.smithypython.customize;

import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.python.codegen.GenerationContext;

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

      writer.write(
          """
             # TODO: Should this extend ApiError...?
             class CollectionOfErrors(ApiError[Literal["CollectionOfErrors"]]):
                 code: Literal["CollectionOfErrors"] = "CollectionOfErrors"
                 message: str
                 # TODO: To add `list` here, I'd need a typehint... what should the object type be? i.e. list[?]
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
                 # TODO: obj *probably* should not have a typehint, so probably no-op here, but I should think more deeply about this...
                 def __init__(
                     self,
                     *,
                     obj
                 ):
                     # TODO: Remove this if I decide this shouldn't extend ApiError
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

}
