package software.amazon.polymorph.smithyrust.generator;

import static software.amazon.polymorph.utils.IOUtils.evalTemplate;
import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toPascalCase;
import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toSnakeCase;

import java.nio.file.Path;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
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
import software.amazon.smithy.model.shapes.UnionShape;
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
    result.addAll(
      model
        .getUnionShapes()
        .stream()
        .filter(this::shouldGenerateEnumForUnion)
        .map(this::unionTypeModule)
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
    result.addAll(
      model
        .getUnionShapes()
        .stream()
        .filter(this::shouldGenerateEnumForUnion)
        .map(this::unionConversionModule)
        .toList()
    );

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
          structureMemberVariables(memberShape)
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
          structureMemberVariables(memberShape)
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

    final String unionModules = model
      .getUnionShapes()
      .stream()
      .filter(this::shouldGenerateEnumForUnion)
      .map(unionShape ->
        IOUtils.evalTemplate(
          """
          mod _$snakeCaseUnionName:L;
          pub use crate::types::_$snakeCaseUnionName:L::$rustUnionName:L;
          """,
          unionVariables(unionShape)
        )
      )
      .collect(Collectors.joining("\n"));
    variables.put("unionModules", unionModules);

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

  private RustFile unionTypeModule(final UnionShape unionShape) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      unionVariables(unionShape)
    );

    final List<MemberShape> memberShapes = unionShape
      .members()
      .stream()
      .toList();

    final String variants = memberShapes
      .stream()
      .map(memberName ->
        IOUtils.evalTemplate(
          """
          #[allow(missing_docs)] // documentation missing in model
          $rustUnionMemberName:L($unionMemberType:L),
          """,
          MapUtils.merge(variables, unionMemberVariables(memberName))
        )
      )
      .collect(Collectors.joining("\n"));
    variables.put("variants", variants);

    final String asImpls = memberShapes
      .stream()
      .map(memberName ->
        IOUtils.evalTemplate(
          """
          /// Tries to convert the enum instance into [`$rustUnionMemberName:L`]($qualifiedRustUnionName:L::$rustUnionMemberName:L), extracting the inner [`$unionMemberType:L`]($unionMemberType:L).
          /// Returns `Err(&Self)` if it can't be converted.
          pub fn as_$snakeCaseUnionMemberName:L(&self) -> ::std::result::Result<&$unionMemberType:L, &Self> {
              if let $qualifiedRustUnionName:L::$rustUnionMemberName:L(val) = &self {
                  ::std::result::Result::Ok(val)
              } else {
                  ::std::result::Result::Err(self)
              }
          }
          """,
          MapUtils.merge(variables, unionMemberVariables(memberName))
        )
      )
      .collect(Collectors.joining("\n"));
    variables.put("asImpls", asImpls);

    final String isImpls = memberShapes
      .stream()
      .map(memberName ->
        IOUtils.evalTemplate(
          """
          /// Returns true if this is a [`$rustUnionMemberName:L`]($qualifiedRustUnionName:L::$rustUnionMemberName:L).
          pub fn is_$snakeCaseUnionMemberName:L(&self) -> ::std::primitive::bool {
              self.as_$snakeCaseUnionMemberName:L().is_ok()
          }
          """,
          MapUtils.merge(variables, unionMemberVariables(memberName))
        )
      )
      .collect(Collectors.joining("\n"));
    variables.put("isImpls", isImpls);

    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/types/union.rs",
      variables
    );
    final Path path = Path.of(
      "src",
      "types",
      "_%s.rs".formatted(toSnakeCase(unionName(unionShape)))
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
    return IOUtils.evalTemplate(
      template,
      structureMemberVariables(memberShape)
    );
  }

  private String structureGetter(final MemberShape memberShape) {
    final Map<String, String> variables = structureMemberVariables(memberShape);
    final String template =
      """
      #[allow(missing_docs)] // documentation missing in model
      pub fn $fieldName:L(&self) -> &::std::option::Option<$fieldType:L> {
          &self.$fieldName:L
      }
      """;
    return IOUtils.evalTemplate(template, variables);
  }

  private String structureBuilderField(final MemberShape memberShape) {
    return IOUtils.evalTemplate(
      "pub(crate) $fieldName:L: ::std::option::Option<$fieldType:L>,",
      structureMemberVariables(memberShape)
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
    return IOUtils.evalTemplate(
      template,
      structureMemberVariables(memberShape)
    );
  }

  private String structureBuilderAssignment(final MemberShape memberShape) {
    return IOUtils.evalTemplate(
      "$fieldName:L: self.$fieldName:L,",
      structureMemberVariables(memberShape)
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
    return IOUtils.evalTemplate(
      template,
      structureMemberVariables(memberShape)
    );
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

  private RustFile unionConversionModule(final UnionShape unionShape) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      unionVariables(unionShape)
    );

    final List<Map<String, String>> perMemberVariables = unionShape
      .members()
      .stream()
      .map(memberShape -> {
        final Map<String, String> memberVariables = MapUtils.merge(
          variables,
          unionMemberVariables(memberShape)
        );
        final Shape targetShape = model.expectShape(memberShape.getTarget());
        memberVariables.put(
          "innerToDafny",
          toDafny(targetShape, "x", false, false).toString()
        );
        memberVariables.put(
          "innerFromDafny",
          fromDafny(targetShape, "x", false, false).toString()
        );
        return memberVariables;
      })
      .toList();

    variables.put(
      "toDafnyVariants",
      perMemberVariables
        .stream()
        .map(memberVariables ->
          IOUtils.evalTemplate(
            """
            $qualifiedRustUnionName:L::$rustUnionMemberName:L(x) =>
                crate::r#$dafnyTypesModuleName:L::$dafnyUnionName:L::$dafnyUnionMemberName:L {
                    $dafnyUnionMemberName:L: $innerToDafny:L,
                },
            """,
            memberVariables
          )
        )
        .collect(Collectors.joining("\n"))
    );
    variables.put(
      "fromDafnyVariants",
      perMemberVariables
        .stream()
        .map(memberVariables ->
          IOUtils.evalTemplate(
            """
            crate::r#$dafnyTypesModuleName:L::$dafnyUnionName:L::$dafnyUnionMemberName:L {
                $dafnyUnionMemberName:L: x @ _,
            } => $qualifiedRustUnionName:L::$rustUnionMemberName:L($innerFromDafny:L),
            """,
            memberVariables
          )
        )
        .collect(Collectors.joining("\n"))
    );

    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/conversions/union.rs",
      variables
    );
    final Path path = Path.of(
      "src",
      "conversions",
      "%s.rs".formatted(toSnakeCase(unionName(unionShape)))
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
      operationVariables(operationShape),
      structureVariables(structureShape)
    );
    variables.put(
      "variants",
      toDafnyVariantsForStructure(structureShape).toString()
    );

    return TokenTree.of(
      evalTemplate(
        """
        #[allow(dead_code)]
        pub fn to_dafny(
            value: crate::operation::$snakeCaseOperationName:L::$rustStructureName:L,
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
      operationVariables(operationShape),
      structureVariables(structureShape)
    );
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
        ) -> crate::operation::$snakeCaseOperationName:L::$rustStructureName:L {
            crate::operation::$snakeCaseOperationName:L::$rustStructureName:L::builder()
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
  private HashMap<String, String> structureMemberVariables(
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

  protected String unionName(final UnionShape unionShape) {
    return unionShape.getId().getName(service);
  }

  protected String rustUnionName(final UnionShape unionShape) {
    return toPascalCase(unionName(unionShape));
  }

  protected String qualifiedRustUnionName(final UnionShape unionShape) {
    return "%s::%s".formatted(
        getRustTypesModuleName(),
        rustUnionName(unionShape)
      );
  }

  /**
   * Generates values for variables commonly used in union-specific templates.
   */
  protected HashMap<String, String> unionVariables(
    final UnionShape unionShape
  ) {
    final HashMap<String, String> variables = new HashMap<>();
    final String unionName = unionName(unionShape);
    variables.put("unionName", unionName);
    variables.put("snakeCaseUnionName", toSnakeCase(unionName));
    variables.put("dafnyUnionName", unionName);
    variables.put("rustUnionName", rustUnionName(unionShape));
    variables.put("qualifiedRustUnionName", qualifiedRustUnionName(unionShape));
    return variables;
  }

  protected String unionMemberName(final MemberShape memberShape) {
    return memberShape.getMemberName();
  }

  protected String rustUnionMemberName(final MemberShape memberShape) {
    return toPascalCase(unionMemberName(memberShape));
  }

  protected String dafnyUnionMemberName(final MemberShape memberShape) {
    return unionMemberName(memberShape);
  }

  /**
   * Generates values for variables commonly used in union-member-specific templates.
   */
  protected HashMap<String, String> unionMemberVariables(
    final MemberShape memberShape
  ) {
    final String memberName = unionMemberName(memberShape);
    final Shape targetShape = model.expectShape(memberShape.getTarget());

    final HashMap<String, String> variables = new HashMap<>();
    variables.put("unionMemberName", memberName);
    variables.put("snakeCaseUnionMemberName", toSnakeCase(memberName));
    variables.put("dafnyUnionMemberName", dafnyUnionMemberName(memberShape));
    variables.put("rustUnionMemberName", rustUnionMemberName(memberShape));
    variables.put("unionMemberType", rustTypeForShape(targetShape));
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
      case UNION -> {
        if (ModelUtils.isInServiceNamespace(shape.getId(), service)) {
          yield qualifiedRustUnionName((UnionShape) shape);
        }
        throw new UnsupportedOperationException(
          "Unsupported type for union: " + shape.getId()
        );
      }
      default -> throw new UnsupportedOperationException(
        "Unsupported shape type: " + shape.getType()
      );
    };
  }

  @Override
  protected TokenTree toDafny(
    final Shape shape,
    final String rustValue,
    boolean isRustOption,
    boolean isDafnyOption
  ) {
    return switch (shape.getType()) {
      case STRING, ENUM -> {
        if (shape.hasTrait(EnumTrait.class) || shape.isEnumShape()) {
          var enumShapeName = toSnakeCase(shape.toShapeId().getName());
          if (isDafnyOption) {
            yield TokenTree.of(
              """
              ::std::rc::Rc::new(match &%s {
                  Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::conversions::%s::to_dafny(x.clone()) },
                  None => crate::_Wrappers_Compile::Option::None { }
              })
              """.formatted(rustValue, enumShapeName)
            );
          } else if (isRustOption) {
            yield TokenTree.of(
              "crate::conversions::%s::to_dafny(%s.clone().unwrap())".formatted(
                  enumShapeName,
                  rustValue
                )
            );
          } else {
            yield TokenTree.of(
              "crate::conversions::%s::to_dafny(%s.clone())".formatted(
                  enumShapeName,
                  rustValue
                )
            );
          }
        } else if (shape.hasTrait(DafnyUtf8BytesTrait.class)) {
          final String rustToDafny =
            "dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(&%s.as_bytes().to_vec(), |b| *b)";
          String valueToDafny;
          if (isRustOption) {
            valueToDafny =
              """
              match %s {
                Some(s) => crate::_Wrappers_Compile::Option::Some { value: %s },
                None => crate::_Wrappers_Compile::Option::None {},
              }""".formatted(rustValue, rustToDafny.formatted("s"));
            if (!isDafnyOption) {
              valueToDafny = "(%s).Extract()".formatted(valueToDafny);
            }
          } else {
            valueToDafny = rustToDafny.formatted(rustValue);
          }
          yield TokenTree.of("::std::rc::Rc::new(%s)".formatted(valueToDafny));
        } else {
          if (isRustOption) {
            var result = TokenTree.of(
              "crate::standard_library_conversions::ostring_to_dafny(&%s)".formatted(
                  rustValue
                )
            );
            if (!isDafnyOption) {
              result = TokenTree.of(result, TokenTree.of(".Extract()"));
            }
            yield result;
          } else {
            yield TokenTree.of(
              "dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&%s)".formatted(
                  rustValue
                )
            );
          }
        }
      }
      case BOOLEAN -> {
        if (isRustOption) {
          yield TokenTree.of(
            "crate::standard_library_conversions::obool_to_dafny(&%s)".formatted(
                rustValue
              )
          );
        } else {
          yield TokenTree.of("%s.clone()".formatted(rustValue));
        }
      }
      case INTEGER -> {
        if (isDafnyOption) {
          if (isRustOption) {
            yield TokenTree.of(
              "crate::standard_library_conversions::oint_to_dafny(%s)".formatted(
                  rustValue
                )
            );
          } else {
            yield TokenTree.of(
              "crate::standard_library_conversions::oint_to_dafny(Some(%s))".formatted(
                  rustValue
                )
            );
          }
        } else {
          yield TokenTree.of("%s.clone()".formatted(rustValue));
        }
      }
      case LONG -> {
        if (isRustOption) {
          yield TokenTree.of(
            "crate::standard_library_conversions::olong_to_dafny(&%s)".formatted(
                rustValue
              )
          );
        } else {
          yield TokenTree.of("%s.clone()".formatted(rustValue));
        }
      }
      case DOUBLE -> {
        if (isRustOption) {
          yield TokenTree.of(
            "crate::standard_library_conversions::odouble_to_dafny(&%s)".formatted(
                rustValue
              )
          );
        } else {
          yield TokenTree.of(
            "crate::standard_library_conversions::double_to_dafny(*%s)".formatted(
                rustValue
              )
          );
        }
      }
      case TIMESTAMP -> {
        if (isRustOption) {
          yield TokenTree.of(
            "crate::standard_library_conversions::otimestamp_to_dafny(&%s)".formatted(
                rustValue
              )
          );
        } else {
          yield TokenTree.of(
            "crate::standard_library_conversions::timestamp_to_dafny(&%s)".formatted(
                rustValue
              )
          );
        }
      }
      case BLOB -> {
        if (isDafnyOption) {
          yield TokenTree.of(
            "crate::standard_library_conversions::oblob_to_dafny(&%s)".formatted(
                rustValue
              )
          );
        } else if (isRustOption) {
          yield TokenTree.of(
            "crate::standard_library_conversions::oblob_to_dafny(&%s).Extract()".formatted(
                rustValue
              )
          );
        } else {
          yield TokenTree.of(
            "crate::standard_library_conversions::blob_to_dafny(&%s)".formatted(
                rustValue
              )
          );
        }
      }
      case LIST -> {
        ListShape listShape = shape.asListShape().get();
        Shape memberShape = model.expectShape(
          listShape.getMember().getTarget()
        );
        if (!isDafnyOption) {
          if (isRustOption) {
            yield TokenTree.of(
              """
              ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(&%s.clone().unwrap(),
                  |e| %s,
              )
              """.formatted(rustValue, toDafny(memberShape, "e", false, false))
            );
          } else {
            yield TokenTree.of(
              """
              ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(&%s,
                  |e| %s,
              )
              """.formatted(rustValue, toDafny(memberShape, "e", false, false))
            );
          }
        } else {
          yield TokenTree.of(
            """
            ::std::rc::Rc::new(match &%s {
                Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
                    ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
                        |e| %s,
                    )
                },
                None => crate::r#_Wrappers_Compile::Option::None {}
            })
            """.formatted(rustValue, toDafny(memberShape, "e", false, false))
          );
        }
      }
      case MAP -> {
        MapShape mapShape = shape.asMapShape().get();
        Shape keyShape = model.expectShape(mapShape.getKey().getTarget());
        Shape valueShape = model.expectShape(mapShape.getValue().getTarget());
        if (!isDafnyOption) {
          if (isRustOption) {
            yield TokenTree.of(
              """
              ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(&%s.clone().unwrap(),
                  |k| %s,
                  |v| %s,
              )
              """.formatted(
                  rustValue,
                  toDafny(keyShape, "k", false, false),
                  toDafny(valueShape, "v", false, false)
                )
            );
          } else {
            yield TokenTree.of(
              """
              ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(&%s.clone(),
                  |k| %s,
                  |v| %s,
              )
              """.formatted(
                  rustValue,
                  toDafny(keyShape, "k", false, false),
                  toDafny(valueShape, "v", false, false)
                )
            );
          }
        } else {
          yield TokenTree.of(
            """

            ::std::rc::Rc::new(match &%s {
                Some(x) => crate::r#_Wrappers_Compile::Option::Some { value :
                    ::dafny_runtime::dafny_runtime_conversions::hashmap_to_dafny_map(x,
                        |k| %s,
                        |v| %s,
                    )
                },
                None => crate::r#_Wrappers_Compile::Option::None {}
            })
            """.formatted(
                rustValue,
                toDafny(keyShape, "k", false, false),
                toDafny(valueShape, "v", false, false)
              )
          );
        }
      }
      case STRUCTURE, UNION -> {
        var structureShapeName = toSnakeCase(shape.getId().getName());
        if (!isDafnyOption) {
          if (isRustOption) {
            yield TokenTree.of(
              """
              crate::conversions::%s::to_dafny(&%s.clone().unwrap())
              """.formatted(structureShapeName, rustValue)
            );
          } else {
            yield TokenTree.of(
              """
              crate::conversions::%s::to_dafny(%s.clone())
              """.formatted(structureShapeName, rustValue)
            );
          }
        } else {
          yield TokenTree.of(
            """
            ::std::rc::Rc::new(match &%s {
                Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::conversions::%s::to_dafny(x.clone()) },
                None => crate::_Wrappers_Compile::Option::None { }
            })
            """.formatted(rustValue, structureShapeName)
          );
        }
      }
      default -> throw new IllegalArgumentException(
        "Unsupported shape type: %s".formatted(shape.getType())
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
