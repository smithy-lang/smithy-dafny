package software.amazon.polymorph.smithyrust.generator;

import software.amazon.polymorph.utils.IOUtils;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.knowledge.OperationIndex;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.model.traits.ErrorTrait;

import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Stream;

import static software.amazon.polymorph.utils.IOUtils.evalTemplate;
import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toSnakeCase;

public abstract class AbstractRustShimGenerator {
  protected final Model model;
  protected final ServiceShape service;
  protected final OperationIndex operationIndex;

  public AbstractRustShimGenerator(Model model, ServiceShape service) {
    this.model = model;
    this.service = service;
    this.operationIndex = new OperationIndex(model);
  }

  public void generate(final Path outputDir) {
    final var rustFiles = rustFiles();
    final LinkedHashMap<Path, TokenTree> tokenTreeMap = new LinkedHashMap<>();
    for (RustFile rustFile : rustFiles) {
      tokenTreeMap.put(rustFile.path(), rustFile.content());
    }
    IOUtils.writeTokenTreesIntoDir(tokenTreeMap, outputDir);
  }

  protected abstract Set<RustFile> rustFiles();

  protected Stream<OperationShape> serviceOperationShapes() {
    return service.getOperations()
      .stream()
      .map(shapeId -> model.expectShape(shapeId, OperationShape.class));
  }

  protected Stream<StructureShape> allErrorShapes() {
    return model
      .getOperationShapes()
      .stream()
      .flatMap(operationShape -> operationShape.getErrors().stream())
      .distinct()
      .map(errorShapeId -> model.expectShape(errorShapeId, StructureShape.class)
      );
  }

  protected boolean shouldGenerateStructForStructure(
    StructureShape structureShape
  ) {
    return (
      !operationIndex.isInputStructure(structureShape) &&
        !operationIndex.isOutputStructure(structureShape) &&
        !structureShape.hasTrait(ErrorTrait.class) &&
        !structureShape.hasTrait(ShapeId.from("smithy.api#trait")) &&
        structureShape
          .getId()
          .getNamespace()
          .equals(service.getId().getNamespace())
    );
  }

  protected boolean shouldGenerateEnumForUnion(UnionShape unionShape) {
    return unionShape
      .getId()
      .getNamespace()
      .equals(service.getId().getNamespace());
  }

  protected RustFile conversionsErrorModule() {
    TokenTree modulesDeclarations = declarePubModules(
      allErrorShapes()
        .map(structureShape -> toSnakeCase(structureShape.getId().getName()))
    );
    Map<String, String> variables = Map.of(
      "dafnyTypesModuleName",
      getDafnyTypesModuleName()
    );
    TokenTree toDafnyOpaqueErrorFunctions = TokenTree.of(
      evalTemplate(
        """
          /// Wraps up an arbitrary Rust Error value as a Dafny Error
          pub fn to_opaque_error<E: ::std::error::Error + 'static>(value: E) ->
            ::std::rc::Rc<crate::r#$dafnyTypesModuleName:L::Error>
          {
              let error_obj: ::dafny_runtime::Object<dyn::std::any::Any> = ::dafny_runtime::Object(Some(
                  ::std::rc::Rc::new(::std::cell::UnsafeCell::new(value)),
              ));
              ::std::rc::Rc::new(
              crate::r#$dafnyTypesModuleName:L::Error::Opaque {
                  obj: error_obj,
              },
            )
          }
          
          /// Wraps up an arbitrary Rust Error value as a Dafny Result<T, Error>.Failure
          pub fn to_opaque_error_result<T: dafny_runtime::DafnyType, E: ::std::error::Error + 'static>(value: E) ->
            ::std::rc::Rc<
              crate::_Wrappers_Compile::Result<
                T,
                ::std::rc::Rc<crate::r#$dafnyTypesModuleName:L::Error>
              >
            >
          {
              ::std::rc::Rc::new(
                  crate::_Wrappers_Compile::Result::Failure {
                      error: to_opaque_error(value),
                  },
              )
          }
          
          """,
        variables
      )
    );
    return new RustFile(
      Path.of("src", "conversions", "error.rs"),
      TokenTree.of(modulesDeclarations, toDafnyOpaqueErrorFunctions)
    );
  }

  protected TokenTree declarePubModules(Stream<String> moduleNames) {
    return TokenTree
      .of(
        moduleNames
          .sorted()
          .map(module -> TokenTree.of("pub mod " + module + ";\n"))
      )
      .lineSeparated();
  }

  protected String getDafnyModuleName() {
    return service.getId().getNamespace().replace(".", "::");
  }

  protected String getDafnyTypesModuleName() {
    return "%s::internaldafny::types".formatted(getDafnyModuleName());
  }
}
