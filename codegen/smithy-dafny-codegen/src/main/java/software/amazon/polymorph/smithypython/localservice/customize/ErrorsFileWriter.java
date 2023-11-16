// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice.customize;

import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import software.amazon.polymorph.smithypython.common.customize.CustomFileWriter;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.smithy.codegen.core.Symbol;
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
  public void customizeFileForServiceShape(
      ServiceShape serviceShape, GenerationContext codegenContext) {
    String moduleName = codegenContext.settings().getModuleName();

    codegenContext.writerDelegator().useFileWriter(moduleName + "/errors.py", "", writer -> {
      writer.addStdlibImport("typing", "Dict");
      writer.addStdlibImport("typing", "Any");
      writer.addStdlibImport("typing", "List");

      // Generate Smithy shapes for each of this service's modelled errors
      TreeSet<StructureShape> deserializingErrorShapes = new TreeSet<StructureShape>(
          codegenContext.model().getStructureShapesWithTrait(ErrorTrait.class)
              .stream()
              .filter(structureShape -> structureShape.getId().getNamespace()
                  .equals(codegenContext.settings().getService().getNamespace()))
              .collect(Collectors.toSet()));
      for (StructureShape errorShape : deserializingErrorShapes) {
        renderError(codegenContext, writer, errorShape);
      }

      // Generate Smithy shapes that wrap each dependency service's modelled and un-modelled errors
      Optional<LocalServiceTrait> maybeLocalServiceTrait = serviceShape.getTrait(LocalServiceTrait.class);
      if (maybeLocalServiceTrait.isPresent()) {
        LocalServiceTrait localServiceTrait = maybeLocalServiceTrait.get();
        Set<ShapeId> serviceDependencyShapeIds = localServiceTrait.getDependencies();
        if (serviceDependencyShapeIds != null) {
          for (ShapeId serviceDependencyShapeId : serviceDependencyShapeIds) {
            renderDependencyWrappingError(codegenContext, writer, serviceDependencyShapeId);
          }
        }
      }

      // Generate Smithy shapes for each of this service's un-modelled errors
      writer.write(
          """
             class CollectionOfErrors(ApiError[Literal["CollectionOfErrors"]]):
                 code: Literal["CollectionOfErrors"] = "CollectionOfErrors"
                 message: str
                 list: List[ServiceError]
                 
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
                             
             class OpaqueError(ApiError[Literal["OpaqueError"]]):
                 code: Literal["OpaqueError"] = "OpaqueError"
                 obj: Any  # As an OpaqueError, type of obj is unknown

                 def __init__(
                     self,
                     *,
                     obj
                 ):
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
  // to be used for our purposes.
  // TODO-Python: Reconcile this with Smithy-Python.
  private void renderError(GenerationContext context, PythonWriter writer, StructureShape shape) {
    writer.addStdlibImport("typing", "Dict");
    writer.addStdlibImport("typing", "Literal");

    String code = shape.getId().getName();
    Symbol symbol = context.symbolProvider().toSymbol(shape);
    Symbol apiError = CodegenUtils.getApiError(context.settings());
    writer.openBlock("class $L($T[Literal[$S]]):", "", symbol.getName(), apiError, code, () -> {
      writer.write("code: Literal[$1S] = $1S", code);
      writer.write("message: str");
    });
    writer.write("");
  }

  // This is lifted from Smithy-Python, where it is not sufficiently customizable
  // to be used for our purposes.
  // TODO-Python: Reconcile this with Smithy-Python.
  private void renderDependencyWrappingError(GenerationContext context, PythonWriter writer, ShapeId serviceDependencyShapeId) {
    writer.addStdlibImport("typing", "Dict");
    writer.addStdlibImport("typing", "Any");
    writer.addStdlibImport("typing", "Literal");

    Shape serviceDependencyShape = context.model().expectShape(serviceDependencyShapeId);
    String code = serviceDependencyShapeId.getName();
    Symbol symbol = context.symbolProvider().toSymbol(serviceDependencyShape);
    Symbol apiError = CodegenUtils.getApiError(context.settings());
    writer.openBlock("class $L($T[Literal[$S]]):", "", code, apiError, code, () -> {
      writer.write("$L: Any", code);
    });
    writer.write("");
  }

}
