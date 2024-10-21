// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice.customize;

import static java.lang.String.format;

import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import software.amazon.polymorph.smithypython.awssdk.nameresolver.AwsSdkNameResolver;
import software.amazon.polymorph.smithypython.common.customize.CustomFileWriter;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/** Extends the Smithy-Python-generated errors.py file by adding Dafny plugin errors. */
public class ErrorsFileWriter implements CustomFileWriter {

  @Override
  public void customizeFileForServiceShape(
    ServiceShape serviceShape,
    GenerationContext codegenContext
  ) {
    String moduleName =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        codegenContext.settings().getService().getNamespace()
      );

    codegenContext
      .writerDelegator()
      .useFileWriter(
        moduleName + "/errors.py",
        "",
        writer -> {
          writer.addStdlibImport("typing", "Dict");
          writer.addStdlibImport("typing", "Any");
          writer.addStdlibImport("typing", "List");

          // Generate Smithy shapes for each of this service's modelled errors
          TreeSet<StructureShape> deserializingErrorShapes = new TreeSet<
            StructureShape
          >(
            codegenContext
              .model()
              .getStructureShapesWithTrait(ErrorTrait.class)
              .stream()
              .filter(structureShape ->
                structureShape
                  .getId()
                  .getNamespace()
                  .equals(codegenContext.settings().getService().getNamespace())
              )
              .collect(Collectors.toSet())
          );
          for (StructureShape errorShape : deserializingErrorShapes) {
            renderError(codegenContext, writer, errorShape);
          }

          // Generate Smithy shapes that wrap each dependency service's modelled and un-modelled
          // errors
          Optional<LocalServiceTrait> maybeLocalServiceTrait =
            serviceShape.getTrait(LocalServiceTrait.class);
          if (maybeLocalServiceTrait.isPresent()) {
            LocalServiceTrait localServiceTrait = maybeLocalServiceTrait.get();
            Set<ShapeId> serviceDependencyShapeIds =
              localServiceTrait.getDependencies();
            if (serviceDependencyShapeIds != null) {
              for (ShapeId serviceDependencyShapeId : serviceDependencyShapeIds) {
                renderDependencyWrappingError(
                  codegenContext,
                  writer,
                  serviceDependencyShapeId
                );
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
                    obj,
                    alt_text
                ):
                    super().__init__("")
                    self.obj = obj
                    self.alt_text = alt_text

                def as_dict(self) -> Dict[str, Any]:
                    ""\"Converts the OpaqueError to a dictionary.

                    The dictionary uses the modeled shape names rather than the parameter names as
                    keys to be mostly compatible with boto3.
                    ""\"
                    return {
                        'message': self.message,
                        'code': self.code,
                        'obj': self.obj,
                        'alt_text': self.alt_text,
                    }

                @staticmethod
                def from_dict(d: Dict[str, Any]) -> "OpaqueError":
                    ""\"Creates a OpaqueError from a dictionary.

                    The dictionary is expected to use the modeled shape names rather than the
                    parameter names as keys to be mostly compatible with boto3.
                    ""\"
                    kwargs: Dict[str, Any] = {
                        'message': d['message'],
                        'obj': d['obj'],
                        'alt_text': d['alt_text']
                    }

                    return OpaqueError(**kwargs)

                def __repr__(self) -> str:
                    result = "OpaqueError("
                    result += f'message={self.message},'
                    if self.message is not None:
                        result += f"message={repr(self.message)}"
                    result += f'obj={self.alt_text}'
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

          // Write error serializer function
          // "serializer" smithy-to-dafny
          writer.write(
            """
            def _smithy_error_to_dafny_error(e: ServiceError):
                ""\"
                Converts the provided native Smithy-modeled error
                into the corresponding Dafny error.
                ""\"
                ${C|}
                 """,
            writer.consumer(w ->
              generateSmithyErrorToDafnyErrorBlock(
                codegenContext,
                serviceShape,
                w
              )
            )
          );
        }
      );
  }

  /**
   * Generate the method body for the `_smithy_error_to_dafny_error` method.
   *
   * @param codegenContext
   * @param serviceShape
   * @param writer
   */
  private void generateSmithyErrorToDafnyErrorBlock(
    GenerationContext codegenContext,
    ServiceShape serviceShape,
    PythonWriter writer
  ) {
    // Write modelled error converters for this service
    TreeSet<ShapeId> errorShapeSet = new TreeSet<ShapeId>(
      codegenContext
        .model()
        .getStructureShapesWithTrait(ErrorTrait.class)
        .stream()
        .filter(structureShape ->
          structureShape
            .getId()
            .getNamespace()
            .equals(codegenContext.settings().getService().getNamespace())
        )
        .map(Shape::getId)
        .collect(Collectors.toSet())
    );
    for (ShapeId errorShapeId : errorShapeSet) {
      SmithyNameResolver.importSmithyGeneratedTypeForShape(
        writer,
        errorShapeId,
        codegenContext
      );
      writer.addStdlibImport("_dafny");
      writer.addStdlibImport(
        DafnyNameResolver.getDafnyPythonTypesModuleNameForShape(
          errorShapeId,
          codegenContext
        )
      );
      writer.write(
        """
        if isinstance(e, $L.$L):
            return $L.$L(message=_dafny.Seq(e.message))
        """,
        SmithyNameResolver.getSmithyGeneratedModelLocationForShape(
          errorShapeId,
          codegenContext
        ),
        errorShapeId.getName(),
        DafnyNameResolver.getDafnyPythonTypesModuleNameForShape(
          errorShapeId,
          codegenContext
        ),
        DafnyNameResolver.getDafnyTypeForError(errorShapeId)
      );
    }

    // Write out wrapping errors for dependencies.
    // This service will generate a dependency-specific error for each dependency.
    // This dependency-specific error generated for only this service, and not for the dependency
    // service;
    //   this error type will wrap any dependency service's error for processing by this service.
    // The Dafny type for this error contains one member: the dependency's name.
    // ex. Dafny type for MyDependency: `Error_MyDependency(Error...) = { MyDependency: ... }`
    // This member's value can take on any of the error types modelled in the dependency.
    // Polymorph will generate a similar error structure in the primary service's errors.py file.
    // ex. Smithy type for MyDependency: `MyDependency(ApiError...) = { MyDependency: ... }`
    Optional<LocalServiceTrait> maybeLocalServiceTrait = serviceShape.getTrait(
      LocalServiceTrait.class
    );
    if (maybeLocalServiceTrait.isPresent()) {
      LocalServiceTrait localServiceTrait = maybeLocalServiceTrait.get();
      Set<ShapeId> serviceDependencyShapeIds =
        localServiceTrait.getDependencies();

      if (serviceDependencyShapeIds != null) {
        for (ShapeId serviceDependencyShapeId : serviceDependencyShapeIds) {
          ServiceShape dependencyServiceShape = codegenContext
            .model()
            .expectShape(serviceDependencyShapeId)
            .asServiceShape()
            .get();

          String nativeToDafnyErrorName;
          if (dependencyServiceShape.hasTrait(LocalServiceTrait.class)) {
            nativeToDafnyErrorName = "_smithy_error_to_dafny_error";
          } else if (AwsSdkNameResolver.isAwsSdkShape(dependencyServiceShape)) {
            nativeToDafnyErrorName = "_sdk_error_to_dafny_error";
          } else {
            throw new IllegalArgumentException(
              "Provided serviceShape is neither localService nor AWS SDK shape: " +
              dependencyServiceShape
            );
          }

          // Import the dependency service's `_smithy_error_to_dafny_error` so this service
          //   can defer error conversion to the dependency
          writer.addStdlibImport(
            SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
              serviceDependencyShapeId.getNamespace(),
              codegenContext.settings()
            ) +
            (AwsSdkNameResolver.isAwsSdkShape(serviceDependencyShapeId)
                ? ".shim"
                : ".errors"),
            nativeToDafnyErrorName,
            SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
              serviceDependencyShapeId.getNamespace()
            ) +
            nativeToDafnyErrorName
          );

          writer.addStdlibImport("_dafny");

          // Import this service's error that wraps the dependency service's errors
          ServiceShape serviceDependencyShape = codegenContext
            .model()
            .expectShape(serviceDependencyShapeId)
            .asServiceShape()
            .get();
          String dependencyErrorName =
            SmithyNameResolver.getSmithyGeneratedTypeForServiceError(
              serviceDependencyShape
            );
          String serviceDependencyErrorDafnyName =
            software.amazon.polymorph.smithydafny.DafnyNameResolver.dafnyTypesModuleName(
              serviceDependencyShape.getId().getNamespace()
            ) +
            ".Error";
          final String errorConstructorName =
            serviceDependencyErrorDafnyName.replace("Types.Error", "");

          // Generate conversion method:
          // "If this is a dependency-specific error, defer to the dependency's
          // `_smithy_error_to_dafny_error`" via
          // if isinstance(e, MyDependency):
          //   return MyService.Error_MyDependency(MyDependency_smithy_error_to_dafny_error(e.message))
          writer.write(
            """
            if isinstance(e, $L):
                return $L.Error_$L($L(e.message))
            """,
            dependencyErrorName,
            DafnyNameResolver.getDafnyPythonTypesModuleNameForShape(
              serviceShape,
              codegenContext
            ),
            errorConstructorName,
            SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
              serviceDependencyShapeId.getNamespace()
            ) +
            nativeToDafnyErrorName
          );
        }
      }
    }

    // Add service-specific CollectionOfErrors
    writer.write(
      """
      if isinstance(e, CollectionOfErrors):
          return $L.Error_CollectionOfErrors(message=_dafny.Seq(e.message), list=_dafny.Seq(
              _smithy_error_to_dafny_error(native_err) for native_err in e.list
          ))
      """,
      DafnyNameResolver.getDafnyPythonTypesModuleNameForShape(
        serviceShape.getId(),
        codegenContext
      )
    );
    writer.addStdlibImport("_dafny");
    // Service-specific OpaqueError; we know it has obj
    writer.write(
      """
      if isinstance(e, OpaqueError):
          return $L.Error_Opaque(obj=e.obj, alt__text=e.alt_text)
      """,
      DafnyNameResolver.getDafnyPythonTypesModuleNameForShape(
        serviceShape.getId(),
        codegenContext
      )
    );
    writer.addStdlibImport(
      DafnyNameResolver.getDafnyGeneratedPathForSmithyNamespace(
        serviceShape.getId().getNamespace()
      )
    );
    writer.addStdlibImport("_dafny");
    // Nothing found, we know nothing about this error. Cast as opaque
    writer.write(
      """
      else:
          return $L.Error_Opaque(obj=e, alt__text=_dafny.Seq(
            "".join(
                [
                    chr(int.from_bytes(pair, "big"))
                    for pair in zip(
                        *[iter(repr(e).encode("utf-16-be"))] * 2
                    )
                ]
            )
        ))
      """,
      DafnyNameResolver.getDafnyPythonTypesModuleNameForShape(
        serviceShape.getId(),
        codegenContext
      )
    );
    writer.addStdlibImport(
      DafnyNameResolver.getDafnyGeneratedPathForSmithyNamespace(
        serviceShape.getId().getNamespace()
      )
    );
  }

  // This is lifted from Smithy-Python.
  // Smithy-Python has no concept of dependencies or other namespaces.
  // This allows errors in other namespaces to be rendered correctly.
  private void renderError(
    GenerationContext context,
    PythonWriter writer,
    StructureShape shape
  ) {
    writer.addStdlibImport("typing", "Dict");
    writer.addStdlibImport("typing", "Literal");

    String code = shape.getId().getName();
    Symbol symbol = context.symbolProvider().toSymbol(shape);
    var apiError = Symbol
      .builder()
      .name("ApiError")
      .namespace(
        format(
          "%s.errors",
          SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
            context.settings().getService().getNamespace(),
            context
          )
        ),
        "."
      )
      .definitionFile(
        format(
          "./%s/errors.py",
          SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
            context.settings().getService().getNamespace()
          )
        )
      )
      .build();
    writer.openBlock(
      "class $L($T[Literal[$S]]):",
      "",
      symbol.getName(),
      apiError,
      code,
      () -> {
        writer.write("code: Literal[$1S] = $1S", code);
        writer.write("message: str");
      }
    );
    writer.write("");
  }

  // This is lifted from Smithy-Python.
  // Smithy-Python has no concept of dependencies or other namespaces.
  // This allows errors in other namespaces to be rendered correctly.
  private void renderDependencyWrappingError(
    GenerationContext context,
    PythonWriter writer,
    ShapeId serviceDependencyShapeId
  ) {
    writer.addStdlibImport("typing", "Dict");
    writer.addStdlibImport("typing", "Any");
    writer.addStdlibImport("typing", "Literal");

    ServiceShape serviceDependencyShape = context
      .model()
      .expectShape(serviceDependencyShapeId)
      .asServiceShape()
      .get();
    String code = SmithyNameResolver.getSmithyGeneratedTypeForServiceError(
      serviceDependencyShape
    );

    var apiError = Symbol
      .builder()
      .name("ApiError")
      .namespace(
        format(
          "%s.errors",
          SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
            context.settings().getService().getNamespace(),
            context
          )
        ),
        "."
      )
      .definitionFile(
        format(
          "./%s/errors.py",
          SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
            context.settings().getService().getNamespace()
          )
        )
      )
      .build();
    writer.openBlock(
      "class $L($T[Literal[$S]]):",
      "",
      code,
      apiError,
      code,
      () -> {
        writer.write("$L: $L", code, "Any");
      }
    );
    writer.write("");
  }
}
