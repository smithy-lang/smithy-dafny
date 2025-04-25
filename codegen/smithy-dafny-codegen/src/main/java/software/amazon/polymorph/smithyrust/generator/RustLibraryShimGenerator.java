package software.amazon.polymorph.smithyrust.generator;

import static software.amazon.polymorph.utils.IOUtils.evalTemplate;
import static software.amazon.polymorph.utils.IOUtils.evalTemplateResource;
import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toPascalCase;
import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toSnakeCase;

import java.math.BigDecimal;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import software.amazon.polymorph.smithydafny.DafnyNameResolver;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.utils.BoundOperationShape;
import software.amazon.polymorph.utils.ConstrainTraitUtils;
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
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.LengthTrait;
import software.amazon.smithy.model.traits.RangeTrait;
import software.amazon.smithy.model.traits.RequiredTrait;
import software.amazon.smithy.model.traits.UnitTypeTrait;

/**
 * Generates all Rust modules needed to wrap a Dafny library as a Rust library.
 */
public class RustLibraryShimGenerator extends AbstractRustShimGenerator {

  private final boolean generateWrappedClient;
  private final RustValidationGenerator validationGenerator;

  public RustLibraryShimGenerator(
    final MergedServicesGenerator mergedGenerator,
    final Model model,
    final ServiceShape service,
    final boolean generateWrappedClient
  ) {
    super(mergedGenerator, model, service);
    this.generateWrappedClient = generateWrappedClient;
    this.validationGenerator = new RustValidationGenerator();
  }

  @Override
  protected Set<RustFile> rustFiles() {
    final Set<RustFile> result = new HashSet<>();

    // client
    result.add(clientModule());
    result.addAll(allOperationClientBuilders());

    // types
    result.add(typesModule());
    result.add(typesConfigModule());
    result.add(typesBuildersModule());
    result.addAll(
      streamStructuresToGenerateStructsFor()
        .map(this::standardStructureModule)
        .toList()
    );
    result.add(typesErrorModule());

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
    result.addAll(
      streamResourcesToGenerateTraitsFor()
        .map(this::resourceTypeModule)
        .toList()
    );

    // validation
    result.add(validationModule());

    // errors
    result.add(errorModule());
    result.add(sealedUnhandledErrorModule());

    // operations
    result.add(operationModule());
    result.addAll(allOperationImplementationModules());

    // conversions
    result.add(conversionsModule());
    result.add(conversionsErrorModule());
    result.add(conversionsClientModule());
    result.addAll(configConversionModules());

    result.addAll(allOperationConversionModules());
    result.addAll(
      streamStructuresToGenerateStructsFor()
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
    result.addAll(
      streamResourcesToGenerateTraitsFor()
        .filter(this::shouldGenerateTraitForResource)
        .map(this::resourceConversionModule)
        .toList()
    );

    // wrapped client
    if (generateWrappedClient) {
      result.add(wrappedModule());
      result.add(wrappedClientModule());
    }

    // deps module
    result.add(depsModule());

    return result;
  }

  @Override
  protected String getRustTypesModuleName() {
    return getRustRootModuleName(service.getId().getNamespace()) + "::types";
  }

  public static final String TOP_LEVEL_MOD_DECLS =
    """
    pub mod client;
    pub mod types;
    /// Common errors and error handling utilities.
    pub mod error;
    /// All operations that this crate can perform.
    pub mod operation;
    pub mod conversions;
    pub mod validation;
    pub mod deps;
    """;

  public static final String TOP_LEVEL_WRAPPED_CLIENT_DECL =
    """
    #[cfg(feature = "wrapped-client")]
    pub mod wrapped;
    """;

  private RustFile depsModule() {
    final TokenTree content;
    if (mergedGenerator.isMainService(service)) {
      content =
        RustUtils.declarePubModules(
          mergedGenerator
            .streamServicesToGenerateFor(model)
            .filter(s -> !mergedGenerator.isMainService(s))
            .map(s -> s.getId().getNamespace())
            .map(RustUtils::rustModuleForSmithyNamespace)
        );
    } else {
      content = RustUtils.declarePubModules(Stream.empty());
    }
    return new RustFile(rootPathForShape(service).resolve("deps.rs"), content);
  }

  @Override
  protected boolean shouldGenerateStructForStructure(
    final StructureShape structureShape
  ) {
    return (
      super.shouldGenerateStructForStructure(structureShape) &&
      // don't generate a structure for the config structures
      !localServiceTrait(service)
        .getConfigId()
        .equals(structureShape.getId()) &&
      !structureShape.hasTrait(PositionalTrait.class)
    );
  }

  @Override
  protected RustFile conversionsModule() {
    final RustFile file = super.conversionsModule();
    final StructureShape configShape = ModelUtils.getConfigShape(
      model,
      service
    );
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
      service
        .getOperations()
        .stream()
        .map(id -> model.expectShape(id, OperationShape.class))
        .map(operationShape ->
          "mod %s;".formatted(toSnakeCase(operationName(operationShape)))
        )
        .collect(Collectors.joining("\n\n"))
    );

    final StructureShape configShape = ModelUtils.getConfigShape(
      model,
      service
    );
    variables.put(
      "inputValidationFunctionName",
      RustValidationGenerator.shapeValidationFunctionName(
        null,
        null,
        configShape
      )
    );

    final String content = evalTemplateResource(
      getClass(),
      "runtimes/rust/client.rs",
      variables
    );
    return new RustFile(
      rootPathForShape(service).resolve("client.rs"),
      TokenTree.of(content)
    );
  }

  protected RustFile conversionsClientModule() {
    TokenTree clientConversionFunctions = TokenTree.of(
      evalTemplateResource(
        getClass(),
        "runtimes/rust/conversions/client_localservice.rs",
        serviceVariables()
      )
    );
    return new RustFile(
      rootPathForShape(service).resolve("conversions").resolve("client.rs"),
      TokenTree.of(clientConversionFunctions)
    );
  }

  private Set<RustFile> allOperationClientBuilders() {
    return streamAllBoundOperationShapes()
      .map(this::boundOperationClientBuilder)
      .collect(Collectors.toSet());
  }

  private RustFile boundOperationClientBuilder(
    final BoundOperationShape boundOperationShape
  ) {
    final Shape bindingShape = boundOperationShape.bindingShape();
    final OperationShape operationShape = boundOperationShape.operationShape();

    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(bindingShape, operationShape)
    );
    variables.put(
      "builderSettersDoc",
      operationClientBuilderSettersDoc(bindingShape, operationShape)
    );
    variables.put(
      "outputDoc",
      operationClientOutputDoc(bindingShape, operationShape)
    );
    final String content = evalTemplateResource(
      getClass(),
      "runtimes/rust/operation/operation_builder.rs",
      variables
    );
    final Path path = bindingShape.isServiceShape()
      ? rootPathForShape(bindingShape)
        .resolve("client")
        .resolve(variables.get("snakeCaseOperationName") + ".rs")
      : rootPathForShape(bindingShape)
        .resolve("types")
        .resolve(variables.get("operationTargetName"))
        .resolve(variables.get("snakeCaseOperationName") + ".rs");
    return new RustFile(path, TokenTree.of(content));
  }

  private String operationClientBuilderSettersDoc(
    final Shape bindingShape,
    final OperationShape operationShape
  ) {
    final StructureShape inputShape = model.expectShape(
      operationShape.getInputShape(),
      StructureShape.class
    );
    final Map<String, String> opVariables = operationVariables(
      bindingShape,
      operationShape
    );
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
        return evalTemplate(template, variables);
      })
      .collect(Collectors.joining("\n"));
  }

  private String operationClientOutputDoc(
    final Shape bindingShape,
    final OperationShape operationShape
  ) {
    final StructureShape outputShape = model.expectShape(
      operationShape.getOutputShape(),
      StructureShape.class
    );
    final Map<String, String> opVariables = operationVariables(
      bindingShape,
      operationShape
    );
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
        return evalTemplate(template, variables);
      })
      .collect(Collectors.joining("\n"));
  }

  private RustFile typesModule() {
    final Map<String, String> variables = serviceVariables();
    final String namespace = service.getId().getNamespace();

    final String resourceModules = streamResourcesToGenerateTraitsFor()
      .filter(o -> o.getId().getNamespace().equals(namespace))
      .sorted()
      .map(resourceShape ->
        evalTemplate(
          """
          pub mod $snakeCaseResourceName:L;
          pub use $snakeCaseResourceName:L::$rustResourceName:L;
          """,
          resourceVariables(resourceShape)
        )
      )
      .collect(Collectors.joining("\n"));
    variables.put("resourceModules", resourceModules);

    final String structureModules = streamStructuresToGenerateStructsFor()
      .filter(o -> o.getId().getNamespace().equals(namespace))
      .sorted()
      .map(structureShape ->
        evalTemplate(
          """
          mod _$snakeCaseStructureName:L;
          pub use $rustTypesModuleName:L::_$snakeCaseStructureName:L::$rustStructureName:L;
          """,
          MapUtils.merge(variables, structureVariables(structureShape))
        )
      )
      .collect(Collectors.joining("\n"));
    variables.put("structureModules", structureModules);

    final String enumModules = ModelUtils
      .streamEnumShapes(model, service.getId().getNamespace())
      .filter(o -> o.getId().getNamespace().equals(namespace))
      .sorted()
      .map(enumShape ->
        evalTemplate(
          """
          mod _$snakeCaseEnumName:L;
          pub use $rustTypesModuleName:L::_$snakeCaseEnumName:L::$rustEnumName:L;
          """,
          MapUtils.merge(variables, enumVariables(enumShape))
        )
      )
      .collect(Collectors.joining("\n"));
    variables.put("enumModules", enumModules);

    final String unionModules = model
      .getUnionShapes()
      .stream()
      .filter(this::shouldGenerateEnumForUnion)
      .filter(o -> o.getId().getNamespace().equals(namespace))
      .sorted()
      .map(unionShape ->
        evalTemplate(
          """
          mod _$snakeCaseUnionName:L;
          pub use $rustTypesModuleName:L::_$snakeCaseUnionName:L::$rustUnionName:L;
          """,
          MapUtils.merge(variables, unionVariables(unionShape))
        )
      )
      .collect(Collectors.joining("\n"));
    variables.put("unionModules", unionModules);

    final String content = evalTemplateResource(
      getClass(),
      "runtimes/rust/types.rs",
      variables
    );
    return new RustFile(
      rootPathForNamespace(namespace).resolve("types.rs"),
      TokenTree.of(content)
    );
  }

  private RustFile typesConfigModule() {
    final StructureShape configShape = ModelUtils.getConfigShape(
      model,
      service
    );
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      standardStructureVariables(configShape),
      structureModuleVariables(configShape)
    );
    final String content = evalTemplateResource(
      getClass(),
      "runtimes/rust/types/config.rs",
      variables
    );
    final Path path = rootPathForShape(service)
      .resolve("types")
      .resolve("%s.rs".formatted(variables.get("snakeCaseConfigName")));
    return new RustFile(path, TokenTree.of(content));
  }

  private RustFile typesBuildersModule() {
    final Map<String, String> variables = serviceVariables();
    final String content = streamStructuresToGenerateStructsFor()
      .filter(s -> ModelUtils.isInServiceNamespace(s, service))
      .map(structureShape ->
        evalTemplate(
          "pub use $rustTypesModuleName:L::_$snakeCaseStructureName:L::$rustStructureName:LBuilder;",
          MapUtils.merge(variables, structureVariables(structureShape))
        )
      )
      .collect(Collectors.joining("\n\n"));
    final Path path = rootPathForShape(service)
      .resolve("types")
      .resolve("builders.rs");
    return new RustFile(path, TokenTree.of(content));
  }

  private RustFile typesErrorModule() {
    final Map<String, String> variables = serviceVariables();
    final Stream<String> directErrorVariants = allErrorShapes()
      .map(errorShape ->
        evalTemplate(
          docFromShape(errorShape) +
          "\n" +
          """
          $rustErrorName:L {
              message: ::std::string::String,
          },
          """,
          MapUtils.merge(variables, errorVariables(errorShape))
        )
      );
    final Stream<ServiceShape> dependencies =
      ModelUtils.streamLocalServiceDependencies(model, service);
    final Stream<String> dependencyErrorVariants =
      dependencies.map(dependentService -> {
        return evalTemplate(
          """
          $rustErrorName:L {
              error: $rustDependentRootModuleName:L::types::error::Error,
          },
          """,
          MapUtils.merge(
            variables,
            dependentServiceErrorVariables(service, dependentService)
          )
        );
      });
    final String modeledErrorVariants = Stream
      .concat(directErrorVariants, dependencyErrorVariants)
      .collect(Collectors.joining("\n\n"));
    variables.put("modeledErrorVariants", modeledErrorVariants);

    final String content = evalTemplateResource(
      getClass(),
      "runtimes/rust/types/error.rs",
      variables
    );

    final Path path = rootPathForShape(service)
      .resolve("types")
      .resolve("error.rs");

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
        evalTemplate(
          "$rustEnumName:L::$rustEnumMemberName:L => write!(f, \"$enumMemberName:L\"),",
          MapUtils.merge(variables, enumMemberVariables(memberName))
        )
      )
      .collect(Collectors.joining("\n"));
    variables.put("displayVariants", displayVariants);

    final String content = evalTemplateResource(
      getClass(),
      "runtimes/rust/types/enum.rs",
      variables
    );

    final Path path = rootPathForShape(service)
      .resolve("types")
      .resolve("_%s.rs".formatted(toSnakeCase(enumName(enumShape))));
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
        evalTemplate(
          docFromShape(memberName) +
          "\n" +
          """
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
        evalTemplate(
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
        evalTemplate(
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

    final String content = evalTemplateResource(
      getClass(),
      "runtimes/rust/types/union.rs",
      variables
    );
    final Path path = rootPathForShape(service)
      .resolve("types")
      .resolve("_%s.rs".formatted(toSnakeCase(unionName(unionShape))));
    return new RustFile(path, TokenTree.of(content));
  }

  private RustFile resourceTypeModule(final ResourceShape resourceShape) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      resourceVariables(resourceShape)
    );

    variables.put(
      "resourceOperations",
      resourceShape
        .getAllOperations()
        .stream()
        .map(id -> {
          final OperationShape operationShape = model.expectShape(
            id,
            OperationShape.class
          );
          final Map<String, String> operationVariables = MapUtils.merge(
            variables,
            operationVariables(resourceShape, operationShape)
          );
          return evalTemplateResource(
            getClass(),
            "runtimes/rust/types/resource_operation.rs",
            operationVariables
          );
        })
        .collect(Collectors.joining("\n\n"))
    );
    variables.put(
      "operationModules",
      resourceShape
        .getAllOperations()
        .stream()
        .map(shapeId -> model.expectShape(shapeId, OperationShape.class))
        .map(operationShape ->
          "mod %s;".formatted(toSnakeCase(operationName(operationShape)))
        )
        .collect(Collectors.joining("\n\n"))
    );

    final String content = evalTemplateResource(
      getClass(),
      "runtimes/rust/types/resource.rs",
      variables
    );
    final Path path = rootPathForShape(service)
      .resolve("types")
      .resolve("%s.rs".formatted(toSnakeCase(resourceName(resourceShape))));
    return new RustFile(path, TokenTree.of(content));
  }

  private RustFile operationModule() {
    final String content = operationBindingIndex
      .getAllBindingShapes()
      .stream()
      // Need to filter by the binding shape, not the operation shape
      .filter(bindingShape ->
        ModelUtils.isInServiceNamespace(bindingShape, service)
      )
      .flatMap(this::operationModuleDeclarationForBindingShape)
      .sorted()
      .collect(Collectors.joining("\n\n"));
    return new RustFile(
      rootPathForShape(service).resolve("operation.rs"),
      TokenTree.of(content)
    );
  }

  private Stream<String> operationModuleDeclarationForBindingShape(
    final Shape bindingShape
  ) {
    final String opTemplate =
      """
      /// Types for the `$operationName:L` operation.
      pub mod $snakeCaseOperationName:L;
      """;
    return operationBindingIndex
      .getOperations(bindingShape)
      .stream()
      .map(o -> operationVariables(bindingShape, o.operationShape()))
      .map(opVariables -> evalTemplate(opTemplate, opVariables));
  }

  private Set<RustFile> allOperationImplementationModules() {
    return streamAllBoundOperationShapes()
      .flatMap(bo -> boundOperationImplementationModules(bo).stream())
      .collect(Collectors.toSet());
  }

  private Set<RustFile> boundOperationImplementationModules(
    final BoundOperationShape boundOperationShape
  ) {
    final Shape bindingShape = boundOperationShape.bindingShape();
    final OperationShape operationShape = boundOperationShape.operationShape();

    final StructureShape inputShape = model.expectShape(
      operationShape.getInputShape(),
      StructureShape.class
    );
    final StructureShape outputShape = model.expectShape(
      operationShape.getOutputShape(),
      StructureShape.class
    );
    return Set.of(
      operationOuterModule(bindingShape, operationShape, inputShape),
      operationStructureModule(bindingShape, operationShape, inputShape),
      operationStructureModule(bindingShape, operationShape, outputShape),
      operationBuildersModule(bindingShape, operationShape)
    );
  }

  private RustFile operationOuterModule(
    final Shape bindingShape,
    final OperationShape operationShape,
    final StructureShape inputShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(bindingShape, operationShape)
    );
    variables.put(
      "inputValidationFunctionName",
      RustValidationGenerator.shapeValidationFunctionName(
        bindingShape,
        operationShape,
        inputShape
      )
    );
    if (bindingShape.isServiceShape()) {
      if (inputShape.hasTrait(PositionalTrait.class)) {
        // Need to fetch the single member and then convert,
        // since on the Rust side there is still an input structure
        // but not on the Dafny side.
        final MemberShape onlyMember = PositionalTrait.onlyMember(inputShape);
        final String rustValue =
          "input.r#" + toSnakeCase(onlyMember.getMemberName());
        variables.put(
          "inputToDafny",
          toDafny(inputShape, rustValue, true, false).toString()
        );
      } else if (inputShape.hasTrait(UnitTypeTrait.class)) {
        variables.put("inputToDafny", "()");
      } else {
        variables.put(
          "inputToDafny",
          evalTemplate(
            "$rustRootModuleName:L::conversions::$snakeCaseOperationName:L::_$snakeCaseSyntheticOperationInputName:L::to_dafny(input)",
            variables
          )
        );
      }

      StructureShape outputShape = operationIndex
        .getOutputShape(operationShape)
        .get();
      if (outputShape.hasTrait(PositionalTrait.class)) {
        variables.put(
          "outputFromDafny",
          fromDafny(outputShape, "inner_result.value()", false, false)
            .toString()
        );
      } else if (outputShape.hasTrait(UnitTypeTrait.class)) {
        variables.put("outputFromDafny", "()");
      } else {
        variables.put(
          "outputFromDafny",
          evalTemplate(
            "$rustRootModuleName:L::conversions::$snakeCaseOperationName:L::_$snakeCaseSyntheticOperationOutputName:L::from_dafny(inner_result.value().clone())",
            variables
          )
        );
      }

      variables.put(
        "innerInput",
        inputShape.hasTrait(UnitTypeTrait.class) ? "" : "&inner_input"
      );

      variables.put(
        "operationSendBody",
        evalTemplateResource(
          getClass(),
          "runtimes/rust/operation/outer_send_body.rs",
          variables
        )
      );
    } else {
      variables.put(
        "operationSendBody",
        evalTemplate(
          "$snakeCaseResourceName:L.inner.lock().unwrap().$snakeCaseOperationName:L(input)",
          MapUtils.merge(
            variables,
            resourceVariables(bindingShape.asResourceShape().orElseThrow())
          )
        )
      );
    }

    final String content = evalTemplateResource(
      getClass(),
      "runtimes/rust/operation/outer.rs",
      variables
    );

    final String snakeCaseOpName = toSnakeCase(operationName(operationShape));
    final Path path = operationsModuleFilePath(bindingShape)
      .resolve(snakeCaseOpName + ".rs");
    return new RustFile(path, TokenTree.of(content));
  }

  class RustValidationGenerator {

    private final Map<String, String> commonVariables;
    private final Set<Shape> shapesToValidate;

    // map from synthetic input/output shapes to their operations
    private final Map<ShapeId, OperationShape> relatedOperationShapes;

    RustValidationGenerator() {
      this.commonVariables = serviceVariables();
      this.shapesToValidate = new TreeSet<>();
      this.relatedOperationShapes = new HashMap<>();

      // Start from the service config and operation input/outputs
      final var rootShapes = new HashSet<StructureShape>();
      rootShapes.add(ModelUtils.getConfigShape(model, service));
      streamAllBoundOperationShapes()
        .map(BoundOperationShape::operationShape)
        .forEach(operationShape -> {
          final var inputShapeId = operationShape.getInputShape();
          final var outputShapeId = operationShape.getOutputShape();
          rootShapes.add(model.expectShape(inputShapeId, StructureShape.class));
          rootShapes.add(
            model.expectShape(outputShapeId, StructureShape.class)
          );

          relatedOperationShapes.put(inputShapeId, operationShape);
          relatedOperationShapes.put(outputShapeId, operationShape);
        });

      // Traverse to find relevant shapes
      final var queue = new LinkedList<Shape>(rootShapes);
      while (!queue.isEmpty()) {
        final var shape = queue.poll();
        if (shapesToValidate.contains(shape)) {
          continue;
        }
        if (
          !(shape instanceof MemberShape ||
            shape instanceof StructureShape ||
            shape instanceof UnionShape ||
            shape instanceof ListShape ||
            shape instanceof MapShape)
        ) {
          continue;
        }

        shapesToValidate.add(shape);
        if (shape instanceof MemberShape memberShape) {
          queue.add(model.expectShape(memberShape.getTarget()));
        } else {
          queue.addAll(shape.getAllMembers().values());
        }
      }
    }

    Set<Shape> getShapesToValidate() {
      return shapesToValidate;
    }

    private String generateValidationFunctions(final Shape shape) {
      var result = generateValidationFunction(null, null, shape);
      if (operationIndex.isInputStructure(shape)) {
        return (
          result +
          "\n" +
          operationIndex
            .getInputBindings(shape)
            .stream()
            .flatMap(operation ->
              operationBindingIndex.getBoundOperations(operation).stream()
            )
            .map(boundOperation ->
              generateValidationFunction(
                boundOperation.bindingShape(),
                boundOperation.operationShape(),
                shape
              )
            )
            .collect(Collectors.joining("\n"))
        );
      } else if (operationIndex.isOutputStructure(shape)) {
        return (
          result +
          "\n" +
          operationIndex
            .getOutputBindings(shape)
            .stream()
            .flatMap(operation ->
              operationBindingIndex.getBoundOperations(operation).stream()
            )
            .map(boundOperation ->
              generateValidationFunction(
                boundOperation.bindingShape(),
                boundOperation.operationShape(),
                shape
              )
            )
            .collect(Collectors.joining("\n"))
        );
      } else {
        return result;
      }
    }

    /**
     * Generates a validation function for the given aggregate or member shape.
     * <p>
     * Validation of constraints (required, range, and length)
     * occurs only in validation functions for member shapes.
     * Validation functions for aggregate shapes
     * only delegate to the validation functions for their members.
     * <p>
     * Other modules should therefore only call validation functions for aggregate shapes.
     */
    private String generateValidationFunction(
      final Shape bindingShape,
      final OperationShape operation,
      final Shape shape
    ) {
      final var validationBlocks = new ArrayList<String>();

      final var parentShape = shape instanceof MemberShape memberShape
        ? model.expectShape(memberShape.getContainer())
        : null;
      final var isStructureMember =
        parentShape != null && parentShape.isStructureShape();

      if (shape instanceof MemberShape memberShape) {
        memberShape
          .getTrait(RequiredTrait.class)
          .ifPresent(_trait ->
            validationBlocks.add(this.validateRequired(memberShape))
          );
        // For simplicity, avoid wrapping the rest of the validation in a conditional
        if (isStructureMember) {
          validationBlocks.add(
            """
            if input.is_none() {
              return ::std::result::Result::Ok(());
            }
            let input = input.as_ref().unwrap();
            """
          );
        }

        memberShape
          .getMemberTrait(model, RangeTrait.class)
          .ifPresent(trait ->
            validationBlocks.add(this.validateRange(memberShape, trait))
          );
        memberShape
          .getMemberTrait(model, LengthTrait.class)
          .ifPresent(trait ->
            validationBlocks.add(this.validateLength(memberShape, trait))
          );

        // validate target if necessary
        final var targetShape = model.expectShape(memberShape.getTarget());
        if (this.shapesToValidate.contains(targetShape)) {
          final var memberVariables = structureMemberVariables(memberShape);
          memberVariables.put(
            "targetValidationFunctionName",
            shapeValidationFunctionName(null, null, targetShape)
          );
          validationBlocks.add(
            evalTemplate(
              """
              $targetValidationFunctionName:L(input)?;
              """,
              memberVariables
            )
          );
        }
      } else if (shape instanceof StructureShape structureShape) {
        // If this is a response shape for an AWS SDK,
        // make validation a no-op for now.
        // This is because the SDKs will produce values that violate constraints,
        // such as a `Some({})` on an optional map with @length(min: 1).
        // This could be considered an SDK bug since information is lost,
        // SDKs are also not supposed to validate constraints
        // which makes it harder to argue it should be fixed.
        // See https://github.com/smithy-lang/smithy-dafny/issues/751
        var generator = mergedGenerator.generatorForShape(shape);
        if (
          generator instanceof RustAwsSdkShimGenerator &&
          operationIndex.isOutputStructure(shape)
        ) {
          validationBlocks.add(
            "// Validation intentionally suppressed for AWS SDK response structures"
          );
        } else {
          var isPositionalOutput =
            (operation == null ||
              operation.getOutputShape().equals(shape.getId())) &&
            structureShape.hasTrait(PositionalTrait.class);
          for (final var memberShape : structureShape
            .getAllMembers()
            .values()) {
            final var memberVariables = structureMemberVariables(memberShape);
            memberVariables.put(
              "memberValidationFunctionName",
              shapeValidationFunctionName(null, null, memberShape)
            );

            if (isPositionalOutput) {
              validationBlocks.add(
                evalTemplate(
                  "$memberValidationFunctionName:L(&Some(input.clone()))?;",
                  memberVariables
                )
              );
            } else if (
              mergedGenerator
                .generatorForShape(structureShape)
                .isRustFieldRequired(structureShape, memberShape) &&
              // TODO: This may be more correct than the current isRustFieldRequired in general
              !(operationIndex.isOutputStructure(structureShape) &&
                model.expectShape(memberShape.getTarget()).isListShape())
            ) {
              validationBlocks.add(
                evalTemplate(
                  "$memberValidationFunctionName:L(&Some(input.r#$fieldName:L.clone()))?;",
                  memberVariables
                )
              );
            } else {
              validationBlocks.add(
                evalTemplate(
                  "$memberValidationFunctionName:L(&input.r#$fieldName:L)?;",
                  memberVariables
                )
              );
            }
          }
        }
      } else if (shape instanceof UnionShape unionShape) {
        final var unionVariables = unionVariables(unionShape);
        for (final var memberShape : unionShape.getAllMembers().values()) {
          final var memberVariables = MapUtils.merge(
            unionVariables,
            unionMemberVariables(memberShape)
          );
          memberVariables.put(
            "memberValidationFunctionName",
            shapeValidationFunctionName(null, null, memberShape)
          );
          validationBlocks.add(
            evalTemplate(
              """
              if let $qualifiedRustUnionName:L::$rustUnionMemberName:L(ref inner) = &input {
                $memberValidationFunctionName:L(inner)?;
              }
              """,
              memberVariables
            )
          );
        }
      } else if (shape instanceof ListShape listShape) {
        final var memberShape = listShape.getMember();
        final Map<String, String> memberVariables = Map.of(
          "memberValidationFunctionName",
          shapeValidationFunctionName(null, null, memberShape)
        );
        validationBlocks.add(
          evalTemplate(
            """
            for inner in input.iter() {
              $memberValidationFunctionName:L(inner)?;
            }
            """,
            memberVariables
          )
        );
      } else if (shape instanceof MapShape mapShape) {
        final var keyShape = mapShape.getKey();
        final var valueShape = mapShape.getValue();
        final Map<String, String> memberVariables = Map.of(
          "keyValidationFunctionName",
          shapeValidationFunctionName(null, null, keyShape),
          "valueValidationFunctionName",
          shapeValidationFunctionName(null, null, valueShape)
        );
        validationBlocks.add(
          evalTemplate(
            """
            for (inner_key, inner_val) in input.iter() {
              $keyValidationFunctionName:L(inner_key)?;
              $valueValidationFunctionName:L(inner_val)?;
            }
            """,
            memberVariables
          )
        );
      } else {
        throw new IllegalArgumentException(
          "Unsupported shape: " + shape.getId()
        );
      }

      final var variables = new HashMap<String, String>();
      variables.put(
        "shapeValidationFunctionName",
        shapeValidationFunctionName(bindingShape, operation, shape)
      );
      variables.put("validationBlocks", String.join("\n", validationBlocks));

      try {
        if (shape instanceof MemberShape memberShape) {
          final var targetShape = model.expectShape(memberShape.getTarget());
          final var targetType = mergedGeneratorRustTypeForShape(targetShape);
          if (isStructureMember) {
            variables.put(
              "shapeType",
              "::std::option::Option<%s>".formatted(targetType)
            );
          } else {
            variables.put("shapeType", targetType);
          }
        } else if (operation != null) {
          final var operationVariables = mergedGenerator
            .generatorForShape(bindingShape)
            .operationVariables(bindingShape, operation);
          final String shapeType;
          if (operation.getInputShape().equals(shape.getId())) {
            shapeType = operationVariables.get("operationInputType");
          } else {
            shapeType = operationVariables.get("operationOutputType");
          }
          variables.put("shapeType", shapeType);
        } else if (
          ModelUtils
            .getConfigShape(model, service)
            .getId()
            .equals(shape.getId())
        ) {
          // The config shape is a bit special, because even if it's declared in a dependent service
          // we still re-declare it for this one.
          variables.put(
            "shapeType",
            "%s::%s::%s".formatted(
                getRustTypesModuleName(),
                toSnakeCase(rustStructureName((StructureShape) shape)),
                rustStructureName((StructureShape) shape)
              )
          );
        } else {
          variables.put("shapeType", mergedGeneratorRustTypeForShape(shape));
        }
      } catch (Exception e) {
        throw new RuntimeException(
          "Failed on shape %s".formatted(shape.getId()),
          e
        );
      }

      return evalTemplate(
        """
        pub(crate) fn $shapeValidationFunctionName:L(input: &$shapeType:L)
          -> ::std::result::Result<(), ::aws_smithy_types::error::operation::BuildError>
        {
          $validationBlocks:L
          Ok(())
        }
        """,
        variables
      );
    }

    public static String shapeValidationFunctionName(
      final Shape bindingShape,
      final OperationShape operationShape,
      final Shape shape
    ) {
      // the ID foo.bar_baz.quux#My_ShapeName$the_member
      // becomes foo_Pbar__baz_Pquux_HMy__ShapeName_Dthe__member
      // If bindingShape/operationShape is not null (because the shape is the input/output for this operation)
      // the unqualified name is added as a ..._for_<escaped binding name>_<escaped operation name> suffix
      var escapedId = escapedName(shape.getId().toString());
      if (operationShape != null) {
        escapedId =
          escapedId +
          "_for_" +
          escapedName(bindingShape.getId().getName()) +
          "_" +
          escapedName(operationShape.getId().getName());
      }

      return "validate_" + escapedId;
    }

    private static String escapedName(final String name) {
      return name
        .replace("_", "__")
        .replace(".", "_P")
        .replace("#", "_H")
        .replace("$", "_D");
    }

    private String validateRequired(final MemberShape memberShape) {
      return evalTemplate(
        """
        if input.is_none() {
            return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::missing_field(
                "$fieldName:L",
                "$fieldName:L is required but was not specified",
            ));
        }
        """,
        MapUtils.merge(commonVariables, structureMemberVariables(memberShape))
      );
    }

    private String validateRange(
      final MemberShape memberShape,
      final RangeTrait rangeTrait
    ) {
      final var variables = MapUtils.merge(
        commonVariables,
        structureMemberVariables(memberShape)
      );
      final var targetShape = model.expectShape(memberShape.getTarget());
      final var min = rangeTrait
        .getMin()
        .map(bound -> asLiteral(bound, targetShape));
      final var max = rangeTrait
        .getMax()
        .map(bound -> asLiteral(bound, targetShape));

      variables.put(
        "condition",
        "!(%s..%s).contains(input)".formatted(
            min.orElse(""),
            max.map(val -> "=" + val).orElse("")
          )
      );
      variables.put("rangeDescription", describeMinMax(min, max));
      return evalTemplate(
        """
        if $condition:L {
            return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::invalid_field(
                "$fieldName:L",
                "$fieldName:L failed to satisfy constraint: Member must be $rangeDescription:L",
            ));
        }
        """,
        variables
      );
    }

    private String validateLength(
      final MemberShape memberShape,
      final LengthTrait lengthTrait
    ) {
      final var targetShape = model.expectShape(memberShape.getTarget());
      final var len =
        switch (targetShape.getType()) {
          case BLOB -> "input.as_ref().len()";
          case STRING -> targetShape.hasTrait(DafnyUtf8BytesTrait.class)
            // scalar values
            ? "input.chars().count()"
            // The Smithy spec says that this should count scalar values,
            // but for consistency with the existing Java and .NET implementations,
            // we instead count UTF-16 code points.
            // See <https://github.com/smithy-lang/smithy-dafny/issues/610>.
            : "input.chars().map(::std::primitive::char::len_utf16).fold(0usize, ::std::ops::Add::add)";
          default -> "input.len()";
        };
      final var variables = MapUtils.merge(
        commonVariables,
        structureMemberVariables(memberShape)
      );
      final var min = lengthTrait.getMin().map(Object::toString);
      final var max = lengthTrait.getMax().map(Object::toString);
      final var conditionTemplate =
        "!(%s..%s).contains(&%s)".formatted(
            min.orElse(""),
            max.map(val -> "=" + val).orElse(""),
            len
          );
      final var rangeDescription = describeMinMax(min, max);
      return evalTemplate(
        """
        if %s {
            return ::std::result::Result::Err(::aws_smithy_types::error::operation::BuildError::invalid_field(
                "$fieldName:L",
                "$fieldName:L failed to satisfy constraint: Member must have length %s",
            ));
        }
        """.formatted(conditionTemplate, rangeDescription),
        variables
      );
    }

    private String asLiteral(final BigDecimal value, final Shape targetShape) {
      return ConstrainTraitUtils.RangeTraitUtils.asShapeType(
        targetShape,
        value
      );
    }

    @SuppressWarnings("OptionalUsedAsFieldOrParameterType")
    private String describeMinMax(
      final Optional<String> min,
      final Optional<String> max
    ) {
      if (min.isPresent() && max.isPresent()) {
        return "between %s and %s, inclusive".formatted(min.get(), max.get());
      } else if (min.isPresent()) {
        return "greater than or equal to %s".formatted(min.get());
      } else {
        if (max.isEmpty()) {
          throw new IllegalArgumentException(
            "At least one of max and min must be non-null"
          );
        }
        return "less than or equal to %s".formatted(max.get());
      }
    }
  }

  private RustFile operationStructureModule(
    final Shape bindingShape,
    final OperationShape operationShape,
    final StructureShape structureShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(bindingShape, operationShape),
      structureVariables(structureShape),
      structureModuleVariables(structureShape)
    );
    final String content = evalTemplateResource(
      getClass(),
      "runtimes/rust/operation/structure.rs",
      variables
    );
    final Path path = operationModuleFilePath(bindingShape, operationShape)
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
    final String content = evalTemplateResource(
      getClass(),
      "runtimes/rust/types/structure.rs",
      variables
    );
    final Path path = rootPathForShape(service)
      .resolve("types")
      .resolve("_%s.rs".formatted(toSnakeCase(structureName(structureShape))));
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
      docFromShape(memberShape) +
      "\n" +
      """
      pub $safeFieldName:L: ::std::option::Option<$fieldType:L>,
      """;
    return evalTemplate(template, structureMemberVariables(memberShape));
  }

  private String structureGetter(final MemberShape memberShape) {
    final Map<String, String> variables = structureMemberVariables(memberShape);
    final String template =
      docFromShape(memberShape) +
      "\n" +
      """
      pub fn $safeFieldName:L(&self) -> &::std::option::Option<$fieldType:L> {
          &self.$safeFieldName:L
      }
      """;
    return evalTemplate(template, variables);
  }

  private String structureBuilderField(final MemberShape memberShape) {
    return evalTemplate(
      "pub(crate) $safeFieldName:L: ::std::option::Option<$fieldType:L>,",
      structureMemberVariables(memberShape)
    );
  }

  private String structureBuilderAccessors(final MemberShape memberShape) {
    final String template =
      docFromShape(memberShape) +
      "\n" +
      """
      pub fn $safeFieldName:L(mut self, input: impl ::std::convert::Into<$fieldType:L>) -> Self {
          self.$safeFieldName:L = ::std::option::Option::Some(input.into());
          self
      }
      """ +
      docFromShape(memberShape) +
      "\n" +
      """
      pub fn set_$fieldName:L(mut self, input: ::std::option::Option<$fieldType:L>) -> Self {
          self.$safeFieldName:L = input;
          self
      }
      """ +
      docFromShape(memberShape) +
      "\n" +
      """
      pub fn get_$fieldName:L(&self) -> &::std::option::Option<$fieldType:L> {
          &self.$safeFieldName:L
      }
      """;
    return evalTemplate(template, structureMemberVariables(memberShape));
  }

  private String structureBuilderAssignment(final MemberShape memberShape) {
    return evalTemplate(
      "$safeFieldName:L: self.$safeFieldName:L,",
      structureMemberVariables(memberShape)
    );
  }

  private RustFile operationBuildersModule(
    final Shape bindingShape,
    final OperationShape operationShape
  ) {
    final StructureShape inputShape = model.expectShape(
      operationShape.getInputShape(),
      StructureShape.class
    );
    final String accessors = ModelUtils
      .streamStructureMembersSorted(inputShape)
      .map(this::operationFluentBuilderFieldAccessors)
      .collect(Collectors.joining("\n"));

    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(bindingShape, operationShape)
    );
    variables.put("accessors", accessors);

    final String content = evalTemplateResource(
      getClass(),
      "runtimes/rust/operation/builders.rs",
      variables
    );
    final Path path = operationModuleFilePath(bindingShape, operationShape)
      .resolve("builders.rs");
    return new RustFile(path, TokenTree.of(content));
  }

  private String operationFluentBuilderFieldAccessors(
    final MemberShape memberShape
  ) {
    final String template =
      docFromShape(memberShape) +
      "\n" +
      """
      pub fn $safeFieldName:L(mut self, input: impl ::std::convert::Into<$fieldType:L>) -> Self {
          self.inner = self.inner.$safeFieldName:L(input.into());
          self
      }
      """ +
      docFromShape(memberShape) +
      "\n" +
      """
      pub fn set_$fieldName:L(mut self, input: ::std::option::Option<$fieldType:L>) -> Self {
          self.inner = self.inner.set_$fieldName:L(input);
          self
      }
      """ +
      docFromShape(memberShape) +
      "\n" +
      """
      pub fn get_$fieldName:L(&self) -> &::std::option::Option<$fieldType:L> {
          self.inner.get_$fieldName:L()
      }
      """;
    return evalTemplate(template, structureMemberVariables(memberShape));
  }

  private RustFile errorModule() {
    final String content = evalTemplateResource(
      getClass(),
      "runtimes/rust/error.rs",
      Map.of()
    );
    return new RustFile(
      rootPathForShape(service).resolve("error.rs"),
      TokenTree.of(content)
    );
  }

  private RustFile sealedUnhandledErrorModule() {
    final String content = evalTemplateResource(
      getClass(),
      "runtimes/rust/error/sealed_unhandled.rs",
      Map.of()
    );
    return new RustFile(
      rootPathForShape(service).resolve("error").resolve("sealed_unhandled.rs"),
      TokenTree.of(content)
    );
  }

  protected RustFile conversionsErrorModule() {
    final Map<String, String> variables = serviceVariables();

    final Stream<String> directToDafnyArms = allErrorShapes()
      .map(errorShape ->
        evalTemplate(
          """
          $qualifiedRustErrorVariant:L { message } =>
              crate::r#$dafnyTypesModuleName:L::Error::$errorName:L {
                  message: ::dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&message),
              },
          """,
          MapUtils.merge(variables, errorVariables(errorShape))
        )
      );
    final Stream<String> dependencyToDafnyArms = ModelUtils
      .streamLocalServiceDependencies(model, service)
      .map(dependentService ->
        evalTemplate(
          """
          $qualifiedRustErrorVariant:L { error } =>
              crate::r#$dafnyTypesModuleName:L::Error::$errorName:L {
                  $errorName:L: $rustDependentRootModuleName:L::conversions::error::to_dafny(error),
              },
          """,
          MapUtils.merge(
            variables,
            dependentServiceErrorVariables(service, dependentService)
          )
        )
      );
    final String toDafnyArms = Stream
      .concat(directToDafnyArms, dependencyToDafnyArms)
      .collect(Collectors.joining("\n"));
    variables.put("toDafnyArms", toDafnyArms);

    final Stream<String> directFromDafnyArms = allErrorShapes()
      .map(errorShape ->
        evalTemplate(
          """
          crate::r#$dafnyTypesModuleName:L::Error::$errorName:L { message } =>
              $qualifiedRustErrorVariant:L {
                  message: ::dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(&message),
              },
          """,
          MapUtils.merge(variables, errorVariables(errorShape))
        )
      );
    final Stream<String> dependencyFromDafnyArms = ModelUtils
      .streamLocalServiceDependencies(model, service)
      .map(dependentService ->
        evalTemplate(
          """
          crate::r#$dafnyTypesModuleName:L::Error::$errorName:L { $errorName:L } =>
              $qualifiedRustErrorVariant:L {
                  error: $rustDependentRootModuleName:L::conversions::error::from_dafny($errorName:L.clone()),
              },
          """,
          MapUtils.merge(
            variables,
            dependentServiceErrorVariables(service, dependentService)
          )
        )
      );
    final String fromDafnyArms = Stream
      .concat(directFromDafnyArms, dependencyFromDafnyArms)
      .collect(Collectors.joining("\n"));
    variables.put("fromDafnyArms", fromDafnyArms);

    final String libraryContent = evalTemplateResource(
      getClass(),
      "runtimes/rust/conversions/error_library.rs",
      variables
    );
    final String commonContent = evalTemplateResource(
      getClass(),
      "runtimes/rust/conversions/error_common.rs",
      variables
    );
    return new RustFile(
      rootPathForShape(service).resolve("conversions").resolve("error.rs"),
      TokenTree.of(commonContent, libraryContent)
    );
  }

  private Set<RustFile> configConversionModules() {
    final StructureShape configShape = ModelUtils.getConfigShape(
      model,
      service
    );
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      standardStructureVariables(configShape)
    );
    variables.put(
      "variants",
      toDafnyVariantsForStructure(configShape).toString()
    );
    variables.put(
      "fluentMemberSetters",
      fluentMemberSettersForStructure(configShape).toString()
    );
    final String snakeCaseConfigName = variables.get("snakeCaseConfigName");

    final String outerContent = evalTemplateResource(
      getClass(),
      "runtimes/rust/conversions/config.rs",
      variables
    );
    final Path outerPath = rootPathForShape(service)
      .resolve("conversions")
      .resolve("%s.rs".formatted(snakeCaseConfigName));
    final RustFile outerModule = new RustFile(
      outerPath,
      TokenTree.of(outerContent)
    );

    final String innerContent = evalTemplateResource(
      getClass(),
      "runtimes/rust/conversions/config/_config.rs",
      variables
    );
    final Path innerPath = rootPathForShape(service)
      .resolve("conversions")
      .resolve(snakeCaseConfigName)
      .resolve("_%s.rs".formatted(snakeCaseConfigName));
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
    final String content = evalTemplateResource(
      getClass(),
      "runtimes/rust/conversions/standard_structure.rs",
      variables
    );

    final Path path = rootPathForShape(service)
      .resolve("conversions")
      .resolve("%s.rs".formatted(toSnakeCase(structureName(structureShape))));
    return new RustFile(path, TokenTree.of(content));
  }

  private RustFile resourceConversionModule(final ResourceShape resourceShape) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      resourceVariables(resourceShape)
    );

    variables.put(
      "resourceWrapperOperations",
      resourceShape
        .getAllOperations()
        .stream()
        .map(id -> {
          final OperationShape operationShape = model.expectShape(
            id,
            OperationShape.class
          );
          return resourceOperationWrapperImpl(resourceShape, operationShape);
        })
        .collect(Collectors.joining("\n\n"))
    );
    variables.put(
      "resourceDafnyWrapperOperations",
      resourceShape
        .getAllOperations()
        .stream()
        .map(id -> {
          final OperationShape operationShape = model.expectShape(
            id,
            OperationShape.class
          );
          final Map<String, String> operationVariables = MapUtils.merge(
            variables,
            operationVariables(resourceShape, operationShape)
          );
          return resourceOperationDafnyWrapperImpl(
            resourceShape,
            operationShape
          );
        })
        .collect(Collectors.joining("\n\n"))
    );

    final String content = evalTemplateResource(
      getClass(),
      "runtimes/rust/conversions/resource.rs",
      variables
    );
    final Path path = rootPathForShape(service)
      .resolve("conversions")
      .resolve("%s.rs".formatted(toSnakeCase(resourceName(resourceShape))));
    return new RustFile(path, TokenTree.of(content));
  }

  private String resourceOperationWrapperImpl(
    final ResourceShape resourceShape,
    final OperationShape operationShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      resourceVariables(resourceShape),
      operationVariables(resourceShape, operationShape)
    );

    StructureShape inputShape = operationIndex
      .getInputShape(operationShape)
      .get();
    if (inputShape.hasTrait(PositionalTrait.class)) {
      // Need to fetch the single member and then convert,
      // since on the Rust side there is still an input structure
      // but not on the Dafny side.
      final MemberShape onlyMember = PositionalTrait.onlyMember(inputShape);
      final String rustValue = "input.r#" + onlyMember.getMemberName() + "()";
      variables.put(
        "inputFromDafny",
        fromDafny(inputShape, rustValue, false, false).toString()
      );
    } else {
      variables.put(
        "inputFromDafny",
        evalTemplate(
          "$rustRootModuleName:L::conversions::$snakeCaseOperationName:L::_$snakeCaseSyntheticOperationInputName:L::from_dafny(input.clone())",
          variables
        )
      );
    }

    StructureShape outputShape = operationIndex
      .getOutputShape(operationShape)
      .get();
    if (outputShape.hasTrait(PositionalTrait.class)) {
      variables.put(
        "outputToDafny",
        toDafny(outputShape, "x", false, false).toString()
      );
    } else if (outputShape.hasTrait(UnitTypeTrait.class)) {
      variables.put("outputToDafny", "()");
    } else {
      variables.put(
        "outputToDafny",
        evalTemplate(
          "$rustRootModuleName:L::conversions::$snakeCaseOperationName:L::_$snakeCaseSyntheticOperationOutputName:L::to_dafny(x.clone())",
          variables
        )
      );
    }

    return evalTemplateResource(
      getClass(),
      "runtimes/rust/conversions/resource_wrapper_operation.rs",
      variables
    );
  }

  private String resourceOperationDafnyWrapperImpl(
    final ResourceShape resourceShape,
    final OperationShape operationShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      resourceVariables(resourceShape),
      operationVariables(resourceShape, operationShape)
    );

    StructureShape inputShape = operationIndex
      .getInputShape(operationShape)
      .get();
    if (inputShape.hasTrait(PositionalTrait.class)) {
      // Need to fetch the single member and then convert,
      // since on the Rust side there is still an input structure
      // but not on the Dafny side.
      final MemberShape onlyMember = PositionalTrait.onlyMember(inputShape);
      final String rustValue =
        "input.r#" + toSnakeCase(onlyMember.getMemberName());
      variables.put(
        "inputToDafny",
        toDafny(inputShape, rustValue, true, false).toString()
      );
    } else {
      variables.put(
        "inputToDafny",
        evalTemplate(
          "$rustRootModuleName:L::conversions::$snakeCaseOperationName:L::_$snakeCaseSyntheticOperationInputName:L::to_dafny(input)",
          variables
        )
      );
    }

    StructureShape outputShape = operationIndex
      .getOutputShape(operationShape)
      .get();
    if (outputShape.hasTrait(PositionalTrait.class)) {
      variables.put(
        "outputFromDafny",
        fromDafny(outputShape, "inner_result.value()", false, false).toString()
      );
    } else if (outputShape.hasTrait(UnitTypeTrait.class)) {
      variables.put("outputFromDafny", "()");
    } else {
      variables.put(
        "outputFromDafny",
        evalTemplate(
          "$rustRootModuleName:L::conversions::$snakeCaseOperationName:L::_$snakeCaseSyntheticOperationOutputName:L::from_dafny(inner_result.value().clone())",
          variables
        )
      );
    }

    return evalTemplateResource(
      getClass(),
      "runtimes/rust/conversions/resource_dafny_wrapper_operation.rs",
      variables
    );
  }

  @Override
  protected TokenTree operationRequestToDafnyFunction(
    final Shape bindingShape,
    OperationShape operationShape
  ) {
    return operationStructureToDafnyFunction(
      bindingShape,
      operationShape,
      operationShape.getInputShape()
    );
  }

  @Override
  protected TokenTree operationResponseToDafnyFunction(
    final Shape bindingShape,
    final OperationShape operationShape
  ) {
    return operationStructureToDafnyFunction(
      bindingShape,
      operationShape,
      operationShape.getOutputShape()
    );
  }

  private TokenTree operationStructureToDafnyFunction(
    final Shape bindingShape,
    final OperationShape operationShape,
    final ShapeId structureId
  ) {
    final StructureShape structureShape = model.expectShape(
      structureId,
      StructureShape.class
    );
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(bindingShape, operationShape),
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
            value: $rustRootModuleName:L::operation::$snakeCaseOperationName:L::$rustStructureName:L,
        ) -> ::dafny_runtime::Rc<
            crate::r#$dafnyTypesModuleName:L::$structureName:L,
        >{
            ::dafny_runtime::Rc::new(crate::r#$dafnyTypesModuleName:L::$structureName:L::$structureName:L {
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
    final Shape bindingShape,
    final OperationShape operationShape
  ) {
    return operationStructureFromDafnyFunction(
      bindingShape,
      operationShape,
      operationShape.getInputShape()
    );
  }

  @Override
  protected TokenTree operationResponseFromDafnyFunction(
    final Shape bindingShape,
    final OperationShape operationShape
  ) {
    return operationStructureFromDafnyFunction(
      bindingShape,
      operationShape,
      operationShape.getOutputShape()
    );
  }

  private TokenTree operationStructureFromDafnyFunction(
    final Shape bindingShape,
    final OperationShape operationShape,
    final ShapeId structureId
  ) {
    final StructureShape structureShape = model.expectShape(
      structureId,
      StructureShape.class
    );
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(bindingShape, operationShape),
      structureVariables(structureShape)
    );
    variables.put(
      "fluentMemberSetters",
      fluentMemberSettersForStructure(structureShape).toString()
    );

    return TokenTree.of(
      evalTemplate(
        """
        #[allow(dead_code)]
        pub fn from_dafny(
            dafny_value: ::dafny_runtime::Rc<
                crate::r#$dafnyTypesModuleName:L::$structureName:L,
            >,
        ) -> $rustRootModuleName:L::operation::$snakeCaseOperationName:L::$rustStructureName:L {
            $rustRootModuleName:L::operation::$snakeCaseOperationName:L::$rustStructureName:L::builder()
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
    final String content = evalTemplateResource(
      getClass(),
      "runtimes/rust/wrapped.rs",
      serviceVariables()
    );
    return new RustFile(
      rootPathForShape(service).resolve("wrapped.rs"),
      TokenTree.of(content)
    );
  }

  private RustFile wrappedClientModule() {
    final Map<String, String> variables = serviceVariables();
    variables.put(
      "operationImpls",
      operationBindingIndex
        .getOperations(service)
        .stream()
        .map(o -> wrappedClientOperationImpl(service, o.operationShape()))
        .collect(Collectors.joining("\n\n"))
    );
    final String content = evalTemplateResource(
      getClass(),
      "runtimes/rust/wrapped/client.rs",
      variables
    );
    return new RustFile(
      rootPathForShape(service).resolve("wrapped").resolve("client.rs"),
      TokenTree.of(content)
    );
  }

  private String wrappedClientOperationImpl(
    final ServiceShape serviceShape,
    final OperationShape operationShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(serviceShape, operationShape)
    );

    StructureShape inputShape = operationIndex
      .getInputShape(operationShape)
      .get();
    if (inputShape.hasTrait(PositionalTrait.class)) {
      // Need to wrap the single member after converting,
      // since on the Rust side there is still an input structure
      // but not on the Dafny side.
      final MemberShape onlyMember = PositionalTrait.onlyMember(inputShape);
      variables.put("memberName", toSnakeCase(onlyMember.getMemberName()));
      variables.put(
        "dafnyValue",
        fromDafny(inputShape, "input", true, false).toString()
      );
      variables.put(
        "inputFromDafny",
        evalTemplate(
          """
          $rustRootModuleName:L::operation::$snakeCaseOperationName:L::_$snakeCaseSyntheticOperationInputName:L::$syntheticOperationInputName:L {
            $memberName:L: $dafnyValue:L
          }
          """,
          variables
        )
      );
    } else if (inputShape.hasTrait(UnitTypeTrait.class)) {
      variables.put("inputFromDafny", "()");
    } else {
      variables.put(
        "inputFromDafny",
        evalTemplate(
          "$rustRootModuleName:L::conversions::$snakeCaseOperationName:L::_$snakeCaseSyntheticOperationInputName:L::from_dafny(input.clone())",
          variables
        )
      );
    }
    variables.put("operationInputDafnyType", dafnyTypeForShape(inputShape));

    StructureShape outputShape = operationIndex
      .getOutputShape(operationShape)
      .get();
    if (outputShape.hasTrait(PositionalTrait.class)) {
      variables.put(
        "outputToDafny",
        toDafny(outputShape, "inner_result", false, false).toString()
      );
    } else if (outputShape.hasTrait(UnitTypeTrait.class)) {
      variables.put("outputToDafny", "()");
    } else {
      variables.put(
        "outputToDafny",
        evalTemplate(
          "$rustRootModuleName:L::conversions::$snakeCaseOperationName:L::_$snakeCaseSyntheticOperationOutputName:L::to_dafny(inner_result)",
          variables
        )
      );
    }
    variables.put("operationOutputDafnyType", dafnyTypeForShape(outputShape));

    final String selfParameter = "&self,";
    if (inputShape.hasTrait(UnitTypeTrait.class)) {
      variables.put("operationInputParams", selfParameter);
    } else {
      variables.put(
        "operationInputParams",
        selfParameter +
        "\n        input: &" +
        variables.get("operationInputDafnyType") +
        ","
      );
    }

    return evalTemplateResource(
      getClass(),
      "runtimes/rust/wrapped/client_operation_impl.part.rs",
      variables
    );
  }

  private RustFile validationModule() {
    final var validationFunctions = validationGenerator
      .getShapesToValidate()
      .stream()
      .map(validationGenerator::generateValidationFunctions)
      .collect(Collectors.joining("\n"));

    return new RustFile(
      rootPathForShape(service).resolve("validation.rs"),
      TokenTree.of(validationFunctions)
    );
  }

  private Path operationsModuleFilePath(final Shape bindingShape) {
    return rootPathForShape(bindingShape).resolve("operation");
  }

  private Path operationModuleFilePath(
    final Shape bindingShape,
    final OperationShape operationShape
  ) {
    return operationsModuleFilePath(bindingShape)
      .resolve(toSnakeCase(operationName(operationShape)));
  }

  private LocalServiceTrait localServiceTrait(final ServiceShape serviceShape) {
    return serviceShape.expectTrait(LocalServiceTrait.class);
  }

  @Override
  protected HashMap<String, String> serviceVariables() {
    final HashMap<String, String> variables = super.serviceVariables();

    final StructureShape configShape = ModelUtils.getConfigShape(
      model,
      service
    );
    final String configName = configShape.getId().getName(service);
    final String snakeCaseConfigName = toSnakeCase(configName);

    variables.put("configName", configName);
    variables.put("snakeCaseConfigName", snakeCaseConfigName);
    variables.put(
      "qualifiedRustConfigName",
      String.join(
        "::",
        getRustTypesModuleName(),
        snakeCaseConfigName,
        configName
      )
    );
    variables.put("rustErrorModuleName", rustErrorModuleName());
    variables.put(
      "qualifiedRustServiceErrorType",
      qualifiedRustServiceErrorType()
    );

    return variables;
  }

  protected String getSdkId() {
    final LocalServiceTrait localServiceTrait = localServiceTrait(service);
    return localServiceTrait.getSdkId();
  }

  @Override
  protected String syntheticOperationInputName(OperationShape operationShape) {
    return operationName(operationShape) + "Input";
  }

  @Override
  protected String syntheticOperationOutputName(OperationShape operationShape) {
    return operationName(operationShape) + "Output";
  }

  private Map<String, String> dependentServiceErrorVariables(
    final ServiceShape serviceShape,
    final ServiceShape dependentServiceShape
  ) {
    final Map<String, String> variables = new HashMap<>();
    final String rustErrorName =
      dependentServiceShape.getId().getName() + "Error";
    variables.put(
      "errorName",
      DafnyNameResolver.dafnyBaseModuleName(
        dependentServiceShape.getId().getNamespace()
      )
    );
    variables.put("rustErrorName", rustErrorName);
    variables.put(
      "rustDependentRootModuleName",
      mergedGenerator
        .generatorForShape(dependentServiceShape)
        .getRustRootModuleName(dependentServiceShape.getId().getNamespace())
    );
    variables.put(
      "qualifiedRustErrorVariant",
      "%s::%s".formatted(qualifiedRustServiceErrorType(), rustErrorName)
    );
    return variables;
  }

  protected String rustErrorModuleName() {
    return "%s::error".formatted(getRustTypesModuleName());
  }

  protected String qualifiedRustServiceErrorType() {
    return "%s::Error".formatted(rustErrorModuleName());
  }

  protected String errorName(final StructureShape errorShape) {
    return errorShape.getId().getName(service);
  }

  protected String rustErrorName(final StructureShape errorShape) {
    return toPascalCase(errorName(errorShape));
  }

  protected HashMap<String, String> errorVariables(
    final StructureShape errorShape
  ) {
    final HashMap<String, String> variables = new HashMap<>();
    final String errorName = errorName(errorShape);
    final String rustErrorName = rustErrorName(errorShape);
    variables.put("errorName", errorName);
    variables.put("snakeCaseErrorName", toSnakeCase(errorName));
    variables.put("rustErrorName", rustErrorName);
    variables.put(
      "qualifiedRustErrorVariant",
      "%s::%s".formatted(qualifiedRustServiceErrorType(), rustErrorName)
    );
    return variables;
  }

  protected boolean isRustFieldRequired(
    final StructureShape parent,
    final MemberShape member
  ) {
    // We're currently always wrapping all structure members with Option<...>,
    // but this may change with https://github.com/smithy-lang/smithy-dafny/issues/533.
    return false;
  }

  @Override
  protected TokenTree toDafny(
    final Shape originalShape,
    final String rustValue,
    boolean isRustOption,
    boolean isDafnyOption
  ) {
    // First handle the indirection of @reference to service or resource shapes
    final ModelUtils.ResolvedShapeId resolvedShapeId = ModelUtils.resolveShape(
      originalShape,
      model
    );
    final Shape shape = model.expectShape(resolvedShapeId.resolvedId());

    return switch (shape.getType()) {
      case STRING, ENUM -> {
        if (shape.hasTrait(EnumTrait.class) || shape.isEnumShape()) {
          var enumShapeName = toSnakeCase(shape.toShapeId().getName());
          String prefix = topLevelNameForShape(shape);
          if (isDafnyOption) {
            yield TokenTree.of(
              """
              ::dafny_runtime::Rc::new(match &%s {
                  Some(x) => crate::_Wrappers_Compile::Option::Some { value: %s::conversions::%s::to_dafny(x.clone()) },
                  None => crate::_Wrappers_Compile::Option::None { }
              })
              """.formatted(rustValue, prefix, enumShapeName)
            );
          } else if (isRustOption) {
            yield TokenTree.of(
              "%s::conversions::%s::to_dafny(%s.clone().unwrap())".formatted(
                  prefix,
                  enumShapeName,
                  rustValue
                )
            );
          } else {
            yield TokenTree.of(
              "%s::conversions::%s::to_dafny(%s.clone())".formatted(
                  prefix,
                  enumShapeName,
                  rustValue
                )
            );
          }
        } else if (shape.hasTrait(DafnyUtf8BytesTrait.class)) {
          final String rustToDafny =
            "dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(&%s.as_bytes().to_vec(), |b| *b)";
          if (!isRustOption) {
            yield TokenTree.of(rustToDafny.formatted(rustValue));
          }
          final String coercion = isDafnyOption ? "into()" : "Extract()";
          yield TokenTree.of(
            """
            dafny_runtime::Rc::new(match %s {
              Some(s) => crate::_Wrappers_Compile::Option::Some { value: %s },
              None => crate::_Wrappers_Compile::Option::None {},
            }).%s""".formatted(rustValue, rustToDafny.formatted("s"), coercion)
          );
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
        if (isDafnyOption) {
          if (isRustOption) {
            yield TokenTree.of(
              "crate::standard_library_conversions::obool_to_dafny(&%s)".formatted(
                  rustValue
                )
            );
          } else {
            yield TokenTree.of(
              "crate::standard_library_conversions::obool_to_dafny(Some(%s))".formatted(
                  rustValue
                )
            );
          }
        } else {
          if (isRustOption) {
            yield TokenTree.of("%s.clone().unwrap()".formatted(rustValue));
          } else {
            yield TokenTree.of("%s.clone()".formatted(rustValue));
          }
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
          if (isRustOption) {
            yield TokenTree.of("%s.clone().unwrap()".formatted(rustValue));
          } else {
            yield TokenTree.of("%s.clone()".formatted(rustValue));
          }
        }
      }
      case LONG -> {
        if (isDafnyOption) {
          if (isRustOption) {
            yield TokenTree.of(
              "crate::standard_library_conversions::olong_to_dafny(&%s)".formatted(
                  rustValue
                )
            );
          } else {
            yield TokenTree.of(
              "crate::standard_library_conversions::olong_to_dafny(Some(%s))".formatted(
                  rustValue
                )
            );
          }
        } else {
          if (isRustOption) {
            yield TokenTree.of("%s.clone().unwrap()".formatted(rustValue));
          } else {
            yield TokenTree.of("%s.clone()".formatted(rustValue));
          }
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
          if (isRustOption) {
            yield TokenTree.of(
              "crate::standard_library_conversions::oblob_to_dafny(&%s)".formatted(
                  rustValue
                )
            );
          } else {
            yield TokenTree.of(
              "crate::standard_library_conversions::oblob_to_dafny(Some(&%s))".formatted(
                  rustValue
                )
            );
          }
        } else {
          if (isRustOption) {
            yield TokenTree.of(
              "crate::standard_library_conversions::blob_to_dafny(&%s.unwrap())".formatted(
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
            ::dafny_runtime::Rc::new(match &%s {
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

            ::dafny_runtime::Rc::new(match &%s {
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
        var conversionsModule = mergedGenerator
          .generatorForShape(shape)
          .getRustConversionsModuleNameForShape(shape);
        if (!isDafnyOption) {
          if (isRustOption) {
            yield TokenTree.of(
              """
              %s::to_dafny(&%s.clone().unwrap())
              """.formatted(conversionsModule, rustValue)
            );
          } else {
            yield TokenTree.of(
              """
              %s::to_dafny(&%s.clone())
              """.formatted(conversionsModule, rustValue)
            );
          }
        } else {
          yield TokenTree.of(
            """
            ::dafny_runtime::Rc::new(match &%s {
                Some(x) => crate::_Wrappers_Compile::Option::Some { value: %s::to_dafny(&x.clone()) },
                None => crate::_Wrappers_Compile::Option::None { }
            })
            """.formatted(rustValue, conversionsModule)
          );
        }
      }
      case RESOURCE -> {
        String resourceShapeName = toSnakeCase(
          resourceName(shape.asResourceShape().get())
        );
        String prefix = topLevelNameForShape(shape);
        if (!isDafnyOption) {
          if (isRustOption) {
            yield TokenTree.of(
              """
              %s::conversions::%s::to_dafny(&%s.clone().unwrap())
              """.formatted(prefix, resourceShapeName, rustValue)
            );
          } else {
            yield TokenTree.of(
              """
              %s::conversions::%s::to_dafny(&%s.clone())
              """.formatted(prefix, resourceShapeName, rustValue)
            );
          }
        } else {
          yield TokenTree.of(
            """
            ::dafny_runtime::Rc::new(match &%s {
                Some(x) => crate::_Wrappers_Compile::Option::Some { value: %s::conversions::%s::to_dafny(&x.clone()) },
                None => crate::_Wrappers_Compile::Option::None { }
            })
            """.formatted(rustValue, prefix, resourceShapeName)
          );
        }
      }
      case SERVICE -> {
        String prefix = topLevelNameForShape(shape);
        if (!isDafnyOption) {
          if (isRustOption) {
            yield TokenTree.of(
              """
              %s::conversions::client::to_dafny(&%s.clone().unwrap())
              """.formatted(prefix, rustValue)
            );
          } else {
            yield TokenTree.of(
              """
              %s::conversions::client::to_dafny(&%s.clone())
              """.formatted(prefix, rustValue)
            );
          }
        } else {
          yield TokenTree.of(
            """
            ::dafny_runtime::Rc::new(match &%s {
                Some(x) => crate::_Wrappers_Compile::Option::Some { value: %s::conversions::client::to_dafny(&x.clone()) },
                None => crate::_Wrappers_Compile::Option::None { }
            })
            """.formatted(rustValue, prefix)
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

  @Override
  public TokenTree topLevelModuleDeclarations() {
    final TokenTree common = TokenTree.of(TOP_LEVEL_MOD_DECLS);
    return generateWrappedClient
      ? TokenTree
        .of(common, TokenTree.of(TOP_LEVEL_WRAPPED_CLIENT_DECL))
        .lineSeparated()
      : common;
  }
}
