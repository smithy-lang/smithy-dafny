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
import software.amazon.polymorph.utils.Token;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.EnumShape;
import software.amazon.smithy.model.shapes.ListShape;
import software.amazon.smithy.model.shapes.MapShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.EnumTrait;

/**
 * Generates all Rust modules needed to wrap a Dafny library as a Rust library.
 */
public class RustLibraryShimGenerator extends AbstractRustShimGenerator {

  private final StructureShape configShape;

  public RustLibraryShimGenerator(
    final Model model,
    final ServiceShape service
  ) {
    super(model, service);
    // Check assumptions
    final ShapeId configId = service
      .expectTrait(LocalServiceTrait.class)
      .getConfigId();
    configShape = model.expectShape(configId, StructureShape.class);
    if (!configShape.getMemberNames().isEmpty()) {
      throw new UnsupportedOperationException(
        "localService config structures with members aren't supported yet"
      );
    }
  }

  @Override
  protected Set<RustFile> rustFiles() {
    final Set<RustFile> result = new HashSet<>();

    // client
    result.add(clientModule());
    result.addAll(serviceOperationClientBuilders());

    // types
    result.add(typesModule());
    result.add(typesConfigModule());
    result.add(typesBuildersModule());
    result.addAll(
      model
        .getStructureShapes()
        .stream()
        .filter(this::shouldGenerateStructForStructure)
        .map(this::standardStructureModule)
        .toList()
    );
    result.addAll(
      ModelUtils
        .streamEnumShapes(model, service.getId().getNamespace())
        .map(this::enumTypeModule)
        .toList()
    );

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
      model
        .getStructureShapes()
        .stream()
        .filter(this::shouldGenerateStructForStructure)
        .map(this::standardStructureConversionModule)
        .toList()
    );
    result.addAll(
      ModelUtils
        .streamEnumShapes(model, service.getId().getNamespace())
        .map(this::enumConversionModule)
        .toList()
    );
    // TODO union conversion modules

    // wrapped client
    result.add(wrappedModule());
    result.add(wrappedClientModule());

    return result;
  }

  @Override
  protected boolean shouldGenerateStructForStructure(
    final StructureShape structureShape
  ) {
    return (
      super.shouldGenerateStructForStructure(structureShape) &&
      // don't generate a structure for the config structure
      !localServiceTrait().getConfigId().equals(structureShape.getId())
    );
  }

  @Override
  protected RustFile conversionsModule() {
    final RustFile file = super.conversionsModule();
    final TokenTree content = file
      .content()
      .append(
        Token.of(
          "\npub mod %s;".formatted(toSnakeCase(structureName(configShape)))
        )
      );
    return new RustFile(file.path(), content);
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
    final Map<String, String> variables = serviceVariables();

    final String structureModules = model
      .getStructureShapes()
      .stream()
      .filter(this::shouldGenerateStructForStructure)
      .map(structureShape ->
        IOUtils.evalTemplate(
          """
          mod _$snakeCaseStructureName:L;
          pub use crate::types::_$snakeCaseStructureName:L::$rustStructureName:L;
          """,
          structureVariables(structureShape)
        )
      )
      .collect(Collectors.joining("\n"));
    variables.put("structureModules", structureModules);

    final String enumModules = ModelUtils
      .streamEnumShapes(model, service.getId().getNamespace())
      .map(enumShape ->
        IOUtils.evalTemplate(
          """
          mod _$snakeCaseEnumName:L;
          pub use crate::types::_$snakeCaseEnumName:L::$rustEnumName:L;
          """,
          enumVariables(enumShape)
        )
      )
      .collect(Collectors.joining("\n"));
    variables.put("enumModules", enumModules);

    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/types.rs",
      variables
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

  private RustFile typesBuildersModule() {
    final Map<String, String> variables = serviceVariables();
    final String content = model
      .getStructureShapes()
      .stream()
      .filter(this::shouldGenerateStructForStructure)
      .map(structureShape ->
        IOUtils.evalTemplate(
          "pub use $rustTypesModuleName:L::_$snakeCaseStructureName:L::$rustStructureName:LBuilder;",
          MapUtils.merge(variables, structureVariables(structureShape))
        )
      )
      .collect(Collectors.joining("\n\n"));
    final Path path = Path.of("src", "types", "builders.rs");
    return new RustFile(path, TokenTree.of(content));
  }

  private RustFile enumTypeModule(final EnumShape enumShape) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      enumVariables(enumShape)
    );

    final Set<String> memberNames = enumShape.getEnumValues().keySet();

    final String variants = memberNames
      .stream()
      .map(this::rustEnumMemberName)
      .map("%s,"::formatted)
      .collect(Collectors.joining("\n"));
    variables.put("variants", variants);

    final String displayVariants = memberNames
      .stream()
      .map(memberName ->
        IOUtils.evalTemplate(
          "$rustEnumName:L::$rustEnumMemberName:L => write!(f, \"$enumMemberName:L\"),",
          MapUtils.merge(variables, enumMemberVariables(memberName))
        )
      )
      .collect(Collectors.joining("\n"));
    variables.put("displayVariants", displayVariants);

    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/types/enum.rs",
      variables
    );

    final Path path = Path.of(
      "src",
      "types",
      "_%s.rs".formatted(toSnakeCase(enumName(enumShape)))
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
    final StructureShape inputShape = model.expectShape(
      operationShape.getInputShape(),
      StructureShape.class
    );
    final StructureShape outputShape = model.expectShape(
      operationShape.getOutputShape(),
      StructureShape.class
    );
    return Set.of(
      operationOuterModule(operationShape),
      operationStructureModule(operationShape, inputShape),
      operationStructureModule(operationShape, outputShape),
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
    final StructureShape structureShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(operationShape),
      structureVariables(structureShape),
      structureModuleVariables(structureShape)
    );
    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/operation/structure.rs",
      variables
    );
    final Path path = operationModuleFilePath(operationShape)
      .resolve("_%s.rs".formatted(toSnakeCase(structureName(structureShape))));
    return new RustFile(path, TokenTree.of(content));
  }

  private RustFile standardStructureModule(
    final StructureShape structureShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      standardStructureVariables(structureShape),
      structureModuleVariables(structureShape)
    );
    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/types/structure.rs",
      variables
    );
    final Path path = Path.of(
      "src",
      "types",
      "_%s.rs".formatted(toSnakeCase(structureName(structureShape)))
    );
    return new RustFile(path, TokenTree.of(content));
  }

  private Map<String, String> structureModuleVariables(
    final StructureShape structureShape
  ) {
    final List<MemberShape> members = ModelUtils
      .streamStructureMembersSorted(structureShape)
      .toList();
    final String fields = members
      .stream()
      .map(this::structureField)
      .collect(Collectors.joining("\n"));
    final String getters = members
      .stream()
      .map(this::structureGetter)
      .collect(Collectors.joining("\n"));
    final String builderFields = members
      .stream()
      .map(this::structureBuilderField)
      .collect(Collectors.joining("\n"));
    final String builderAccessors = members
      .stream()
      .map(this::structureBuilderAccessors)
      .collect(Collectors.joining("\n"));
    final String builderAssignments = members
      .stream()
      .map(this::structureBuilderAssignment)
      .collect(Collectors.joining("\n"));

    final Map<String, String> variables = new HashMap<>();
    variables.put("fields", fields);
    variables.put("getters", getters);
    variables.put("builderFields", builderFields);
    variables.put("builderAccessors", builderAccessors);
    variables.put("builderAssignments", builderAssignments);
    return variables;
  }

  private String structureField(final MemberShape memberShape) {
    final String template =
      """
      #[allow(missing_docs)] // documentation missing in model
      pub $fieldName:L: ::std::option::Option<$fieldType:L>,
      """;
    return IOUtils.evalTemplate(template, memberVariables(memberShape));
  }

  private String structureGetter(final MemberShape memberShape) {
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

  private String structureBuilderField(final MemberShape memberShape) {
    return IOUtils.evalTemplate(
      "pub(crate) $fieldName:L: ::std::option::Option<$fieldType:L>,",
      memberVariables(memberShape)
    );
  }

  private String structureBuilderAccessors(final MemberShape memberShape) {
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

  private String structureBuilderAssignment(final MemberShape memberShape) {
    return IOUtils.evalTemplate(
      "$fieldName:L: self.$fieldName:L,",
      memberVariables(memberShape)
    );
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

  private RustFile standardStructureConversionModule(
    final StructureShape structureShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      standardStructureVariables(structureShape)
    );
    variables.put(
      "variants",
      toDafnyVariantsForStructure(structureShape).toString()
    );
    variables.put(
      "fluentMemberSetters",
      fluentMemberSettersForStructure(structureShape).toString()
    );
    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/conversions/standard_structure.rs",
      variables
    );

    final Path path = Path.of(
      "src",
      "conversions",
      "%s.rs".formatted(toSnakeCase(structureName(structureShape)))
    );
    return new RustFile(path, TokenTree.of(content));
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
    final String configName = configShape.getId().getName(service);
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

  /**
   * Generates values for variables commonly used in structure-member-specific templates.
   */
  private HashMap<String, String> memberVariables(
    final MemberShape memberShape
  ) {
    final HashMap<String, String> variables = new HashMap<>();
    final String memberName = memberShape.getMemberName();
    variables.put("memberName", memberName);
    variables.put("fieldName", toSnakeCase(memberName));
    variables.put(
      "fieldType",
      rustTypeForShape(model.expectShape(memberShape.getTarget()))
    );
    return variables;
  }

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
      case BLOB -> "::aws_smithy_types::Blob";
      case STRING -> {
        //noinspection deprecation
        if (shape.hasTrait(EnumTrait.class)) {
          yield qualifiedRustEnumType(
            ModelUtils.stringToEnumShape(shape.asStringShape().orElseThrow())
          );
        }
        yield "::std::string::String";
      }
      case ENUM -> qualifiedRustEnumType(shape.asEnumShape().orElseThrow());
      // other simple shapes
      case TIMESTAMP -> "::aws_smithy_types::DateTime";
      // aggregates
      case STRUCTURE -> {
        final StructureShape structureShape = (StructureShape) shape;
        if (shouldGenerateStructForStructure(structureShape)) {
          yield qualifiedRustStructureType(structureShape);
        }
        throw new UnsupportedOperationException(
          "Unsupported type for structure: " + shape.getId()
        );
      }
      case LIST -> {
        final ListShape listShape = (ListShape) shape;
        final String memberType = rustTypeForShape(
          model.expectShape(listShape.getMember().getTarget())
        );
        yield "::std::vec::Vec<%s>".formatted(memberType);
      }
      case MAP -> {
        final MapShape mapShape = (MapShape) shape;
        final String keyType = rustTypeForShape(
          model.expectShape(mapShape.getKey().getTarget())
        );
        final String valueType = rustTypeForShape(
          model.expectShape(mapShape.getValue().getTarget())
        );
        yield "::std::collections::HashMap<%s, %s>".formatted(
            keyType,
            valueType
          );
      }
      // TODO: union
      default -> throw new UnsupportedOperationException(
        "Unsupported shape type: " + shape.getType()
      );
    };
  }

  @Override
  protected boolean isStructureBuilderFallible(
    final StructureShape structureShape
  ) {
    // For simplicity and ease of migration, always make builders fallible.
    return true;
  }
}
