package software.amazon.polymorph.smithyrust.generator;

import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.utils.IOUtils;
import software.amazon.polymorph.utils.MapUtils;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.rust.codegen.core.util.StringsKt;

import java.nio.file.Path;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toSnakeCase;

/**
 * Generates all Rust modules needed to wrap a Dafny library as a Rust library.
 */
public class RustLibraryShimGenerator extends AbstractRustShimGenerator {
  public RustLibraryShimGenerator(Model model, ServiceShape service) {
    super(model, service);

    // Check assumptions
    final ShapeId configId = service.expectTrait(LocalServiceTrait.class).getConfigId();
    if (!model.expectShape(configId).asStructureShape().orElseThrow().getMemberNames().isEmpty()) {
      throw new UnsupportedOperationException("localService config structures with members aren't supported yet");
    }
  }

  @Override
  protected Set<RustFile> rustFiles() {
    ServiceShape service = model.getServiceShapes().stream().findFirst().get();

    Set<RustFile> result = new HashSet<>();
    result.add(libModule());

    // client
    result.add(clientModule());
    result.addAll(serviceOperationClientBuilders());

    // types
    result.add(typesModule());
    result.add(typesConfigModule());

    // errors
    result.add(errorModule());
    result.add(sealedUnhandledErrorModule());
    result.add(conversionsErrorModule());
    result.addAll(
      allErrorShapes()
        .map(errorShape -> errorConversionModule(service, errorShape))
        .collect(Collectors.toSet())
    );

    // operations
    result.add(operationModule());
    result.addAll(serviceOperationImplementationModules());

//    result.addAll(
//      model
//        .getStringShapesWithTrait(EnumTrait.class)
//        .stream()
//        .map(enumShape -> enumConversionModule(service, enumShape))
//        .collect(Collectors.toSet())
//    );

//    result.add(conversionsModuleFile(model, service));
//    result.addAll(allOperationConversionModules());
//    result.addAll(allStructureConversionModules());

    // wrapped client
    result.add(wrappedModule());
    result.add(wrappedClientModule());

    return result;
  }

  private RustFile libModule() {
    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/lib.rs",
      serviceVariables()
    );
    return new RustFile(Path.of("src", "lib.rs"), TokenTree.of(content));
  }

  private RustFile clientModule() {
    final Map<String, String> variables = MapUtils.merge(
      dafnyModuleVariables(),
      serviceVariables()
    );
    variables.put(
      "operationModules",
      serviceOperationShapes()
        .map(operationShape -> "mod %s;".formatted(toSnakeCase(operationName(operationShape))))
        .collect(Collectors.joining("\n\n"))
    );
    final String content = IOUtils.evalTemplate(getClass(), "runtimes/rust/client.rs", variables);
    return new RustFile(Path.of("src", "client.rs"), TokenTree.of(content));
  }

  private Set<RustFile> serviceOperationClientBuilders() {
    return serviceOperationShapes()
      .map(this::operationClientBuilder)
      .collect(Collectors.toSet());
  }

  private RustFile operationClientBuilder(final OperationShape operationShape) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(operationShape)
    );
    variables.put("builderSettersDoc", operationClientBuilderSettersDoc(operationShape));
    variables.put("outputDoc", operationClientOutputDoc(operationShape));
    final String content = IOUtils.evalTemplate(getClass(), "runtimes/rust/client/operation_builder.rs", variables);
    return new RustFile(Path.of("src", "client", variables.get("snakeCaseOperationName") + ".rs"), TokenTree.of(content));
  }

  private String operationClientBuilderSettersDoc(final OperationShape operationShape) {
    final StructureShape inputShape = model.expectShape(operationShape.getInputShape(), StructureShape.class);
    final Map<String, String> opVariables = operationVariables(operationShape);
    final String template =
      """
        ///   - [`$fieldName:L(impl Into<Option<$fieldType:L>>)`](crate::operation::$snakeCaseOperationName:L::builders::$operationName:LFluentBuilder::$fieldName:L) / [`set_$fieldName:L(Option<$fieldType:L>)`](crate::operation::$snakeCaseOperationName:L::builders::$operationName:LFluentBuilder::set_$fieldName:L): (undocumented)<br>""".indent(4);

    return ModelUtils.streamStructureMembersSorted(inputShape).map(memberShape -> {
      final Map<String, String> variables = MapUtils.merge(opVariables, memberVariables(memberShape));
      return IOUtils.evalTemplate(template, variables);
    }).collect(Collectors.joining("\n"));
  }

  private String operationClientOutputDoc(final OperationShape operationShape) {
    final StructureShape outputShape = model.expectShape(operationShape.getOutputShape(), StructureShape.class);
    final Map<String, String> opVariables = operationVariables(operationShape);
    final String template =
      """
        ///   - [`$fieldName:L(Option<$fieldType:L>)`](crate::operation::$snakeCaseOperationName:L::$operationOutputName:L::$fieldName:L): (undocumented)""".indent(4);

    return ModelUtils.streamStructureMembersSorted(outputShape).map(memberShape -> {
      final Map<String, String> variables = MapUtils.merge(opVariables, memberVariables(memberShape));
      return IOUtils.evalTemplate(template, variables);
    }).collect(Collectors.joining("\n"));
  }

  private RustFile typesModule() {
    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/types.rs",
      serviceVariables()
    );
    return new RustFile(Path.of("src", "types.rs"), TokenTree.of(content));
  }

  private RustFile typesConfigModule() {
    final Map<String, String> variables = serviceVariables();
    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/types/config.rs",
      variables
    );
    final Path path = Path.of("src", "types", "%s.rs".formatted(variables.get("snakeCaseConfigName")));
    return new RustFile(path, TokenTree.of(content));
  }

  private RustFile operationModule() {
    final String opTemplate = """
      /// Types for the `$operationName:L` operation.
      pub mod $snakeCaseOperationName:L;
      """;
    final Map<String, String> variables = Map.of(
      "operationModules",
      serviceOperationShapes()
        .map(this::operationVariables)
        .map(opVariables -> IOUtils.evalTemplate(opTemplate, opVariables))
        .collect(Collectors.joining("\n\n"))
    );
    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/operation.rs",
      variables
    );
    return new RustFile(Path.of("src", "operation.rs"), TokenTree.of(content));
  }

  private Set<RustFile> serviceOperationImplementationModules() {
    return serviceOperationShapes()
      .map(this::operationImplementationModules)
      .flatMap(Collection::stream)
      .collect(Collectors.toSet());
  }

  private Set<RustFile> operationImplementationModules(final OperationShape operationShape) {
    return Set.of(
      operationOuterModule(operationShape),
      operationStructureModule(operationShape, operationShape.getInputShape()),
      operationStructureModule(operationShape, operationShape.getOutputShape()),
      operationBuildersModule(operationShape)
    );
  }

  private RustFile operationOuterModule(final OperationShape operationShape) {
    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/operation/outer.rs",
      operationVariables(operationShape)
    );

    final String snakeCaseOpName = toSnakeCase(operationName(operationShape));
    final Path path = operationsModuleFilePath().resolve(snakeCaseOpName + ".rs");
    return new RustFile(path, TokenTree.of(content));
  }

  private RustFile operationStructureModule(final OperationShape operationShape, final ShapeId structureId) {
    final StructureShape structureShape = model.expectShape(structureId, StructureShape.class);
    final String structureName = structureId.getName(service);
    final String snakeCaseStructName = toSnakeCase(structureName);

    final List<MemberShape> members = ModelUtils.streamStructureMembersSorted(structureShape).toList();
    final String fields = members.stream()
      .map(this::operationStructureField)
      .collect(Collectors.joining("\n"));
    final String getters = members.stream()
      .map(this::operationStructureGetter)
      .collect(Collectors.joining("\n"));
    final String builderFields = members.stream()
      .map(this::operationStructureBuilderField)
      .collect(Collectors.joining("\n"));
    final String builderAccessors = members.stream()
      .map(this::operationStructureBuilderAccessors)
      .collect(Collectors.joining("\n"));

    final HashMap<String, String> variables = operationVariables(operationShape);
    variables.put("structureName", structureName);
    variables.put("fields", fields);
    variables.put("getters", getters);
    variables.put("builderFields", builderFields);
    variables.put("builderAccessors", builderAccessors);

    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/operation/structure.rs",
      variables
    );

    final Path path = operationModuleFilePath(operationShape).resolve("_%s.rs".formatted(snakeCaseStructName));
    return new RustFile(path, TokenTree.of(content));
  }

  private String operationStructureField(final MemberShape memberShape) {
    final String template = """
      #[allow(missing_docs)] // documentation missing in model
      pub $fieldName:L: ::std::option::Option<$fieldType:L>,
      """;
    return IOUtils.evalTemplate(template, memberVariables(memberShape));
  }

  private String operationStructureGetter(final MemberShape memberShape) {
    final String template = """
      #[allow(missing_docs)] // documentation missing in model
      pub fn $fieldName:L(&self) -> ::std::option::Option<$fieldType:L> {
          self.$fieldName:L
      }
      """;
    return IOUtils.evalTemplate(template, memberVariables(memberShape));
  }

  private String operationStructureBuilderField(final MemberShape memberShape) {
    final String template = """
      pub(crate) $fieldName:L: ::std::option::Option<$fieldType:L>,
      """;
    return IOUtils.evalTemplate(template, memberVariables(memberShape));
  }

  private String operationStructureBuilderAccessors(final MemberShape memberShape) {
    final String template = """
      #[allow(missing_docs)] // documentation missing in model
      pub fn $fieldName:L(mut self, input: impl ::std::convert::Into<$fieldType:L>) -> Self {
          self.$fieldName:L = ::std::option::Option::Some(input.into());
          self
      }
      #[allow(missing_docs)] // documentation missing in model
      pub fn set_$fieldName:L(mut self, input: ::std::option::Option<$fieldType:L>) -> Self {
          self.$fieldName:L = input;
          self
      }
      #[allow(missing_docs)] // documentation missing in model
      pub fn get_$fieldName:L(&self) -> &::std::option::Option<$fieldType:L> {
          &self.$fieldName:L
      }
      """;
    return IOUtils.evalTemplate(template, memberVariables(memberShape));
  }

  private RustFile operationBuildersModule(final OperationShape operationShape) {
    final StructureShape outputShape = model.expectShape(operationShape.getOutputShape(), StructureShape.class);
    final String accessors = ModelUtils.streamStructureMembersSorted(outputShape)
      .map(this::operationFluentBuilderFieldAccessors)
      .collect(Collectors.joining("\n"));

    final Map<String, String> variables = operationVariables(operationShape);
    variables.put("accessors", accessors);

    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/operation/builders.rs",
      variables
    );
    final Path path = operationModuleFilePath(operationShape).resolve("builders.rs");
    return new RustFile(path, TokenTree.of(content));
  }

  private String operationFluentBuilderFieldAccessors(final MemberShape memberShape) {
    final String template = """
      #[allow(missing_docs)] // documentation missing in model
      pub fn $fieldName:L(mut self, input: impl ::std::convert::Into<$fieldType:L>) -> Self {
          self.inner = self.inner.$fieldName:L(input.into());
          self
      }
      #[allow(missing_docs)] // documentation missing in model
      pub fn set_$fieldName:L(mut self, input: ::std::option::Option<$fieldType:L>) -> Self {
          self.inner = self.inner.set_$fieldName:L(input);
          self
      }
      #[allow(missing_docs)] // documentation missing in model
      pub fn get_$fieldName:L(&self) -> &::std::option::Option<$fieldType:L> {
          self.inner.get_$fieldName:L()
      }
      """;
    return IOUtils.evalTemplate(template, memberVariables(memberShape));
  }

  private RustFile errorModule() {
    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/error.rs",
      Map.of()
    );
    return new RustFile(Path.of("src", "error.rs"), TokenTree.of(content));
  }

  private RustFile sealedUnhandledErrorModule() {
    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/error/sealed_unhandled.rs",
      Map.of()
    );
    return new RustFile(Path.of("src", "error", "sealed_unhandled.rs"), TokenTree.of(content));
  }

  private RustFile errorConversionModule(
    final ServiceShape service,
    final Shape errorStructure
  ) {
    throw new UnsupportedOperationException("Error conversion is not yet implemented for library services");
  }

  private RustFile wrappedModule() {
    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/wrapped.rs",
      MapUtils.merge(serviceVariables(), dafnyModuleVariables())
    );
    return new RustFile(Path.of("src", "wrapped.rs"), TokenTree.of(content));
  }

  private RustFile wrappedClientModule() {
    final Map<String, String> variables = MapUtils.merge(serviceVariables(), dafnyModuleVariables());
    variables.put(
      "operationImpls",
      serviceOperationShapes().map(this::wrappedClientOperationImpl).collect(Collectors.joining("\n\n"))
    );
    // TODO add operation-specific stuff
    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/wrapped/client.rs",
      variables
    );
    return new RustFile(Path.of("src", "wrapped", "client.rs"), TokenTree.of(content));
  }

  private String wrappedClientOperationImpl(final OperationShape operationShape) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      dafnyModuleVariables(),
      operationVariables(operationShape)
    );
    return IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/wrapped/client_operation_impl.part.rs",
      variables
    );
  }

  private String operationName(final OperationShape operationShape) {
    return operationShape.getId().getName(service);
  }

  private String operationInputName(final OperationShape operationShape) {
    return operationShape.getInputShape().getName(service);
  }

  private String operationOutputName(final OperationShape operationShape) {
    return operationShape.getOutputShape().getName(service);
  }

  private Path operationsModuleFilePath() {
    return Path.of("src", "operation");
  }

  private Path operationModuleFilePath(final OperationShape operationShape) {
    return operationsModuleFilePath().resolve(toSnakeCase(operationName(operationShape)));
  }

  private String operationErrorTypeName(final OperationShape operationShape) {
    return "%sError".formatted(operationName(operationShape));
  }

  /**
   * Generates values for variables commonly used in service-specific templates.
   */
  private HashMap<String, String> serviceVariables() {
    final LocalServiceTrait localServiceTrait = service.expectTrait(LocalServiceTrait.class);
    final String sdkId = localServiceTrait.getSdkId();
    final String configName = localServiceTrait.getConfigId().getName(service);

    final HashMap<String, String> variables = new HashMap<>();
    variables.put("serviceName", service.getId().getName(service));
    variables.put("sdkId", sdkId);
    variables.put("configName", configName);
    variables.put("snakeCaseConfigName", toSnakeCase(configName));
    return variables;
  }

  /**
   * Generates values for variables commonly used in operation-specific templates.
   */
  private HashMap<String, String> operationVariables(final OperationShape operationShape) {
    final String opName = operationName(operationShape);
    final String opInputName = operationInputName(operationShape);
    final String opOutputName = operationOutputName(operationShape);
    final String snakeCaseOpName = toSnakeCase(opName);

    final HashMap<String, String> variables = new HashMap<>();
    variables.put("operationName", opName);
    variables.put("operationInputName", opInputName);
    variables.put("operationOutputName", opOutputName);
    variables.put("operationErrorName", operationErrorTypeName(operationShape));
    variables.put("snakeCaseOperationName", snakeCaseOpName);
    variables.put("snakeCaseOperationInputName", toSnakeCase(opInputName));
    variables.put("snakeCaseOperationOutputName", toSnakeCase(opOutputName));
    return variables;
  }

  /**
   * Generates values for variables commonly used in structure-member-specific templates.
   */
  private HashMap<String, String> memberVariables(final MemberShape memberShape) {
    final HashMap<String, String> variables = new HashMap<>();
    variables.put("fieldName", toSnakeCase(memberShape.getMemberName()));
    variables.put("fieldType", rustTypeForShape(model.expectShape(memberShape.getTarget())));
    return variables;
  }

  // Currently only handles simple types, and doesn't account for any traits
  private String rustTypeForShape(final Shape shape) {
    return switch (shape.getType()) {
      case BOOLEAN -> "::std::primitive::bool";
      // integral
      case BYTE -> "::std::primitive::i8";
      case SHORT -> "::std::primitive::i16";
      case INTEGER -> "::std::primitive::i32";
      case LONG -> "::std::primitive::i64";
      // floats
      case FLOAT -> "::std::primitive::f32";
      case DOUBLE -> "::std::primitive::f64";
      // special numerics
      case BIG_INTEGER -> "::num::bigint::BigInt";
      case BIG_DECIMAL -> "::num::rational::BigRational";
      // special collections
      case BLOB -> "::std::vec::Vec<::std::primitive::u8>";
      case STRING -> "::std::string::String";
      // TODO: enum, list, map, structure, union
      default -> throw new UnsupportedOperationException("Unsupported shape type: " + shape.getType());
    };
  }
}
