package software.amazon.polymorph.smithyrust.generator;

import static software.amazon.polymorph.utils.IOUtils.evalTemplate;
import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toSnakeCase;

import java.nio.file.Path;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
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

/**
 * Generates all Rust modules needed to wrap a Dafny library as a Rust library.
 */
public class RustLibraryShimGenerator extends AbstractRustShimGenerator {

  public RustLibraryShimGenerator(Model model, ServiceShape service) {
    super(model, service);
    // Check assumptions
    final ShapeId configId = service
      .expectTrait(LocalServiceTrait.class)
      .getConfigId();
    if (
      !model
        .expectShape(configId)
        .asStructureShape()
        .orElseThrow()
        .getMemberNames()
        .isEmpty()
    ) {
      throw new UnsupportedOperationException(
        "localService config structures with members aren't supported yet"
      );
    }
  }

  @Override
  protected Set<RustFile> rustFiles() {
    ServiceShape service = model.getServiceShapes().stream().findFirst().get();

    Set<RustFile> result = new HashSet<>();

    // client
    result.add(clientModule());
    result.addAll(serviceOperationClientBuilders());

    // types
    result.add(typesModule());
    result.add(typesConfigModule());
    // TODO enum type modules

    // errors
    result.add(errorModule());
    result.add(sealedUnhandledErrorModule());
    result.addAll(
      allErrorShapes()
        .map(errorShape -> errorConversionModule(service, errorShape))
        .collect(Collectors.toSet())
    );

    // operations
    result.add(operationModule());
    result.addAll(serviceOperationImplementationModules());

    // conversions
    result.add(conversionsModule());
    result.add(conversionsErrorModule());
    result.addAll(configConversionModules());
    result.addAll(allOperationConversionModules());
    result.addAll(
      ModelUtils
        .streamEnumShapes(model, service.getId().getNamespace())
        .map(this::enumConversionModule)
        .toList()
    );
    // TODO structure conversion modules
    // TODO union conversion modules

    // wrapped client
    result.add(wrappedModule());
    result.add(wrappedClientModule());

    return result;
  }

  private RustFile clientModule() {
    final Map<String, String> variables = serviceVariables();
    variables.put(
      "operationModules",
      serviceOperationShapes()
        .map(operationShape ->
          "mod %s;".formatted(toSnakeCase(operationName(operationShape)))
        )
        .collect(Collectors.joining("\n\n"))
    );
    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/client.rs",
      variables
    );
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
    variables.put(
      "builderSettersDoc",
      operationClientBuilderSettersDoc(operationShape)
    );
    variables.put("outputDoc", operationClientOutputDoc(operationShape));
    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/client/operation_builder.rs",
      variables
    );
    return new RustFile(
      Path.of("src", "client", variables.get("snakeCaseOperationName") + ".rs"),
      TokenTree.of(content)
    );
  }

  private String operationClientBuilderSettersDoc(
    final OperationShape operationShape
  ) {
    final StructureShape inputShape = model.expectShape(
      operationShape.getInputShape(),
      StructureShape.class
    );
    final Map<String, String> opVariables = operationVariables(operationShape);
    final String template =
      """
      ///   - [`$fieldName:L(impl Into<Option<$fieldType:L>>)`](crate::operation::$snakeCaseOperationName:L::builders::$operationName:LFluentBuilder::$fieldName:L) / [`set_$fieldName:L(Option<$fieldType:L>)`](crate::operation::$snakeCaseOperationName:L::builders::$operationName:LFluentBuilder::set_$fieldName:L): (undocumented)<br>""".indent(
          4
        );

    return ModelUtils
      .streamStructureMembersSorted(inputShape)
      .map(memberShape -> {
        final Map<String, String> variables = MapUtils.merge(
          opVariables,
          memberVariables(memberShape)
        );
        return IOUtils.evalTemplate(template, variables);
      })
      .collect(Collectors.joining("\n"));
  }

  private String operationClientOutputDoc(final OperationShape operationShape) {
    final StructureShape outputShape = model.expectShape(
      operationShape.getOutputShape(),
      StructureShape.class
    );
    final Map<String, String> opVariables = operationVariables(operationShape);
    final String template =
      """
      ///   - [`$fieldName:L(Option<$fieldType:L>)`](crate::operation::$snakeCaseOperationName:L::$operationOutputName:L::$fieldName:L): (undocumented)""".indent(
          4
        );

    return ModelUtils
      .streamStructureMembersSorted(outputShape)
      .map(memberShape -> {
        final Map<String, String> variables = MapUtils.merge(
          opVariables,
          memberVariables(memberShape)
        );
        return IOUtils.evalTemplate(template, variables);
      })
      .collect(Collectors.joining("\n"));
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
    final Path path = Path.of(
      "src",
      "types",
      "%s.rs".formatted(variables.get("snakeCaseConfigName"))
    );
    return new RustFile(path, TokenTree.of(content));
  }

  private RustFile operationModule() {
    final String opTemplate =
      """
      /// Types for the `$operationName:L` operation.
      pub mod $snakeCaseOperationName:L;
      """;
    final String content = serviceOperationShapes()
      .map(this::operationVariables)
      .map(opVariables -> IOUtils.evalTemplate(opTemplate, opVariables))
      .collect(Collectors.joining("\n\n"));
    return new RustFile(Path.of("src", "operation.rs"), TokenTree.of(content));
  }

  private Set<RustFile> serviceOperationImplementationModules() {
    return serviceOperationShapes()
      .map(this::operationImplementationModules)
      .flatMap(Collection::stream)
      .collect(Collectors.toSet());
  }

  private Set<RustFile> operationImplementationModules(
    final OperationShape operationShape
  ) {
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
    final Path path = operationsModuleFilePath()
      .resolve(snakeCaseOpName + ".rs");
    return new RustFile(path, TokenTree.of(content));
  }

  private RustFile operationStructureModule(
    final OperationShape operationShape,
    final ShapeId structureId
  ) {
    final StructureShape structureShape = model.expectShape(
      structureId,
      StructureShape.class
    );
    final String structureName = structureId.getName(service);
    final String snakeCaseStructName = toSnakeCase(structureName);

    final List<MemberShape> members = ModelUtils
      .streamStructureMembersSorted(structureShape)
      .toList();
    final String fields = members
      .stream()
      .map(this::operationStructureField)
      .collect(Collectors.joining("\n"));
    final String getters = members
      .stream()
      .map(this::operationStructureGetter)
      .collect(Collectors.joining("\n"));
    final String builderFields = members
      .stream()
      .map(this::operationStructureBuilderField)
      .collect(Collectors.joining("\n"));
    final String builderAccessors = members
      .stream()
      .map(this::operationStructureBuilderAccessors)
      .collect(Collectors.joining("\n"));

    final HashMap<String, String> variables = operationVariables(
      operationShape
    );
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

    final Path path = operationModuleFilePath(operationShape)
      .resolve("_%s.rs".formatted(snakeCaseStructName));
    return new RustFile(path, TokenTree.of(content));
  }

  private String operationStructureField(final MemberShape memberShape) {
    final String template =
      """
      #[allow(missing_docs)] // documentation missing in model
      pub $fieldName:L: ::std::option::Option<$fieldType:L>,
      """;
    return IOUtils.evalTemplate(template, memberVariables(memberShape));
  }

  private String operationStructureGetter(final MemberShape memberShape) {
    final Map<String, String> variables = memberVariables(memberShape);

    // for some simple shapes, the Rust runtime types are not Copy
    final Shape targetShape = model.expectShape(memberShape.getTarget());
    final boolean needsClone =
      targetShape.isBlobShape() || targetShape.isStringShape();
    variables.put("fieldClone", needsClone ? ".clone()" : "");

    final String template =
      """
      #[allow(missing_docs)] // documentation missing in model
      pub fn $fieldName:L(&self) -> ::std::option::Option<$fieldType:L> {
          self.$fieldName:L$fieldClone:L
      }
      """;
    return IOUtils.evalTemplate(template, variables);
  }

  private String operationStructureBuilderField(final MemberShape memberShape) {
    final String template =
      """
      pub(crate) $fieldName:L: ::std::option::Option<$fieldType:L>,
      """;
    return IOUtils.evalTemplate(template, memberVariables(memberShape));
  }

  private String operationStructureBuilderAccessors(
    final MemberShape memberShape
  ) {
    final String template =
      """
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

  private RustFile operationBuildersModule(
    final OperationShape operationShape
  ) {
    final StructureShape outputShape = model.expectShape(
      operationShape.getOutputShape(),
      StructureShape.class
    );
    final String accessors = ModelUtils
      .streamStructureMembersSorted(outputShape)
      .map(this::operationFluentBuilderFieldAccessors)
      .collect(Collectors.joining("\n"));

    final Map<String, String> variables = operationVariables(operationShape);
    variables.put("accessors", accessors);

    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/operation/builders.rs",
      variables
    );
    final Path path = operationModuleFilePath(operationShape)
      .resolve("builders.rs");
    return new RustFile(path, TokenTree.of(content));
  }

  private String operationFluentBuilderFieldAccessors(
    final MemberShape memberShape
  ) {
    final String template =
      """
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
    return new RustFile(
      Path.of("src", "error", "sealed_unhandled.rs"),
      TokenTree.of(content)
    );
  }

  @SuppressWarnings("unused")
  private RustFile errorConversionModule(
    final ServiceShape service,
    final Shape errorStructure
  ) {
    throw new UnsupportedOperationException(
      "Error conversion is not yet implemented for library services"
    );
  }

  private Set<RustFile> configConversionModules() {
    final Map<String, String> variables = serviceVariables();
    final String snakeCaseConfigName = variables.get("snakeCaseConfigName");

    final String outerContent = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/conversions/config.rs",
      variables
    );
    final Path outerPath = Path.of(
      "src",
      "conversions",
      "%s.rs".formatted(snakeCaseConfigName)
    );
    final RustFile outerModule = new RustFile(
      outerPath,
      TokenTree.of(outerContent)
    );

    final String innerContent = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/conversions/config/_config.rs",
      variables
    );
    final Path innerPath = Path.of(
      "src",
      "conversions",
      snakeCaseConfigName,
      "_%s.rs".formatted(snakeCaseConfigName)
    );
    final RustFile innerModule = new RustFile(
      innerPath,
      TokenTree.of(innerContent)
    );

    return Set.of(outerModule, innerModule);
  }

  @Override
  protected Set<RustFile> operationConversionModules(
    final OperationShape operationShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(operationShape)
    );

    final String operationModuleName = toSnakeCase(
      operationName(operationShape)
    );
    final String outerContent = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/conversions/operation.rs",
      variables
    );
    final RustFile outerModule = new RustFile(
      Path.of("src", "conversions", operationModuleName + ".rs"),
      TokenTree.of(outerContent)
    );

    final RustFile requestModule = operationRequestConversionModule(
      operationShape
    );
    final RustFile responseModule = operationResponseConversionModule(
      operationShape
    );

    return Set.of(outerModule, requestModule, responseModule);
  }

  @Override
  protected TokenTree operationRequestToDafnyFunction(
    OperationShape operationShape
  ) {
    return operationStructureToDafnyFunction(
      operationShape,
      operationShape.getInputShape()
    );
  }

  @Override
  protected TokenTree operationResponseToDafnyFunction(
    OperationShape operationShape
  ) {
    return operationStructureToDafnyFunction(
      operationShape,
      operationShape.getOutputShape()
    );
  }

  private TokenTree operationStructureToDafnyFunction(
    final OperationShape operationShape,
    final ShapeId structureId
  ) {
    final StructureShape structureShape = model.expectShape(
      structureId,
      StructureShape.class
    );
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(operationShape)
    );
    variables.put("structureName", structureId.getName(service));
    variables.put(
      "variants",
      toDafnyVariantsForStructure(structureShape).toString()
    );

    return TokenTree.of(
      evalTemplate(
        """
        #[allow(dead_code)]
        pub fn to_dafny(
            value: crate::operation::$snakeCaseOperationName:L::$structureName:L,
        ) -> ::std::rc::Rc<
            crate::r#$dafnyTypesModuleName:L::$structureName:L,
        >{
            ::std::rc::Rc::new(crate::r#$dafnyTypesModuleName:L::$structureName:L::$structureName:L {
                $variants:L
            })
        }
        """,
        variables
      )
    );
  }

  @Override
  protected TokenTree operationRequestFromDafnyFunction(
    OperationShape operationShape
  ) {
    return operationStructureFromDafnyFunction(
      operationShape,
      operationShape.getInputShape()
    );
  }

  @Override
  protected TokenTree operationResponseFromDafnyFunction(
    OperationShape operationShape
  ) {
    return operationStructureFromDafnyFunction(
      operationShape,
      operationShape.getOutputShape()
    );
  }

  private TokenTree operationStructureFromDafnyFunction(
    final OperationShape operationShape,
    final ShapeId structureId
  ) {
    final StructureShape structureShape = model.expectShape(
      structureId,
      StructureShape.class
    );
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(operationShape)
    );
    variables.put("structureName", structureId.getName(service));
    variables.put(
      "fluentMemberSetters",
      fluentMemberSettersForStructure(structureShape).toString()
    );

    // unwrap() is safe as long as the builder is infallible
    return TokenTree.of(
      evalTemplate(
        """
        #[allow(dead_code)]
        pub fn from_dafny(
            dafny_value: ::std::rc::Rc<
                crate::r#$dafnyTypesModuleName:L::$structureName:L,
            >,
        ) -> crate::operation::$snakeCaseOperationName:L::$structureName:L {
            crate::operation::$snakeCaseOperationName:L::$structureName:L::builder()
                $fluentMemberSetters:L
                .build()
                .unwrap()
        }
        """,
        variables
      )
    );
  }

  private RustFile wrappedModule() {
    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/wrapped.rs",
      serviceVariables()
    );
    return new RustFile(Path.of("src", "wrapped.rs"), TokenTree.of(content));
  }

  private RustFile wrappedClientModule() {
    final Map<String, String> variables = serviceVariables();
    variables.put(
      "operationImpls",
      serviceOperationShapes()
        .map(this::wrappedClientOperationImpl)
        .collect(Collectors.joining("\n\n"))
    );
    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/wrapped/client.rs",
      variables
    );
    return new RustFile(
      Path.of("src", "wrapped", "client.rs"),
      TokenTree.of(content)
    );
  }

  private String wrappedClientOperationImpl(
    final OperationShape operationShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(operationShape)
    );
    return IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/wrapped/client_operation_impl.part.rs",
      variables
    );
  }

  private Path operationsModuleFilePath() {
    return Path.of("src", "operation");
  }

  private Path operationModuleFilePath(final OperationShape operationShape) {
    return operationsModuleFilePath()
      .resolve(toSnakeCase(operationName(operationShape)));
  }

  private LocalServiceTrait localServiceTrait() {
    return service.expectTrait(LocalServiceTrait.class);
  }

  @Override
  protected HashMap<String, String> serviceVariables() {
    final HashMap<String, String> variables = super.serviceVariables();

    final LocalServiceTrait localServiceTrait = localServiceTrait();
    final String sdkId = localServiceTrait.getSdkId();
    final String configName = localServiceTrait.getConfigId().getName(service);
    variables.put("sdkId", sdkId);
    variables.put("configName", configName);
    variables.put("snakeCaseConfigName", toSnakeCase(configName));

    return variables;
  }

  @Override
  protected String getRustTypesModuleName() {
    return "crate::types";
  }

  @Override
  protected String syntheticOperationInputName(OperationShape operationShape) {
    return operationName(operationShape) + "Input";
  }

  @Override
  protected String syntheticOperationOutputName(OperationShape operationShape) {
    return operationName(operationShape) + "Output";
  }
}
