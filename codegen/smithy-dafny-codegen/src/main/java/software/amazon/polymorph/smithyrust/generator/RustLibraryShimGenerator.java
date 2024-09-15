package software.amazon.polymorph.smithyrust.generator;

import static software.amazon.polymorph.utils.IOUtils.evalTemplate;
import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toPascalCase;
import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toSnakeCase;

import java.nio.file.Path;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import software.amazon.polymorph.smithydafny.DafnyNameResolver;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.PositionalTrait;
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
import software.amazon.smithy.model.shapes.ResourceShape;
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

  public RustLibraryShimGenerator(
    final MergedServicesGenerator mergedGenerator,
    final Model model,
    final ServiceShape service
  ) {
    super(mergedGenerator, model, service);
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
        .map(this::resourceConversionModule)
        .toList()
    );

    // wrapped client
    result.add(wrappedModule());
    result.add(wrappedClientModule());

    // deps module
    result.add(depsModule());

    return result;
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
    pub mod deps;
    #[cfg(feature = "wrapped-client")]
    pub mod wrapped;
    """;

  private RustFile depsModule() {
    final TokenTree content;
    if (mergedGenerator.isMainService(service)) {
      content =
        RustUtils.declarePubModules(
          mergedGenerator.streamServicesToGenerateFor(model)
            .filter(s -> !mergedGenerator.isMainService(s))
            .map(s -> s.getId().getNamespace())
            .map(RustUtils::rustModuleForSmithyNamespace)
        );
    } else {
      content = RustUtils.declarePubModules(Stream.empty());
    }
    return new RustFile(
      rootPathForShape(service).resolve("deps.rs"),
      content
    );
  }


  @Override
  protected boolean shouldGenerateStructForStructure(
    final StructureShape structureShape
  ) {
    return (
      super.shouldGenerateStructForStructure(structureShape) &&
      // don't generate a structure for the config structures
      !localServiceTrait(service).getConfigId().equals(structureShape.getId())
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
      operationBindingIndex
        .getOperations(service)
        .stream()
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
    return new RustFile(
      rootPathForShape(service).resolve("client.rs"),
      TokenTree.of(content)
    );
  }

  protected RustFile conversionsClientModule() {
    TokenTree clientConversionFunctions = TokenTree.of(
      evalTemplate(
        getClass(),
        "runtimes/rust/conversions/client_localservice.rs",
        serviceVariables()
      )
    );
    return new RustFile(
      rootPathForShape(service)
        .resolve("conversions")
        .resolve("client.rs"),
      TokenTree.of(clientConversionFunctions)
    );
  }

  private Set<RustFile> allOperationClientBuilders() {
    return allOperationShapes()
      .filter(this::shouldGenerateOperation)
      .flatMap(this::operationClientBuilders)
      .collect(Collectors.toSet());
  }

  private Stream<RustFile> operationClientBuilders(
    final OperationShape operationShape
  ) {
    return operationBindingIndex
      .getBindingShapes(operationShape)
      .stream()
      .map(b -> boundOperationClientBuilder(b, operationShape));
  }

  private RustFile boundOperationClientBuilder(
    final Shape bindingShape,
    final OperationShape operationShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(serviceForShape(model, bindingShape)),
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
    final String content = IOUtils.evalTemplate(
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
        return IOUtils.evalTemplate(template, variables);
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
        return IOUtils.evalTemplate(template, variables);
      })
      .collect(Collectors.joining("\n"));
  }

  private RustFile typesModule() {
    final Map<String, String> variables = serviceVariables();
    final String namespace = service.getId().getNamespace();

    final String resourceModules = streamResourcesToGenerateTraitsFor()
      .filter(o -> o.getId().getNamespace().equals(namespace))
      .map(resourceShape ->
        IOUtils.evalTemplate(
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
      .filter(o -> o.getId().getNamespace().equals(namespace))
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
      .filter(o -> o.getId().getNamespace().equals(namespace))
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
    final String content = IOUtils.evalTemplate(
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
        IOUtils.evalTemplate(
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
        IOUtils.evalTemplate(
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
        return IOUtils.evalTemplate(
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

    final String content = IOUtils.evalTemplate(
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
      serviceVariables(serviceForShape(model, enumShape)),
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
      serviceVariables(serviceForShape(model, unionShape)),
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

  private RustFile resourceTypeModule(final ResourceShape resourceShape) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(serviceForShape(model, resourceShape)),
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
          return IOUtils.evalTemplate(
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

    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/types/resource.rs",
      variables
    );
    final Path path = Path.of(
      "src",
      "types",
      "%s.rs".formatted(toSnakeCase(resourceName(resourceShape)))
    );
    return new RustFile(path, TokenTree.of(content));
  }

  private RustFile operationModule() {
    final String content = allOperationShapes()
      .filter(this::shouldGenerateOperation)
      // Need to filter by the binding shape, not the operation shape
      .flatMap(o -> operationBindingIndex.getBindingShapes(o).stream())
      .distinct()
      .filter(bindingShape -> ModelUtils.isInServiceNamespace(bindingShape, service))
      // But then map back to bound operations
      .flatMap(this::operationModuleDeclarationForBindingShape)
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
      .map(o -> operationVariables(bindingShape, o))
      .map(opVariables -> IOUtils.evalTemplate(opTemplate, opVariables));
  }

  private Set<RustFile> allOperationImplementationModules() {
    return allOperationShapes()
      .filter(this::shouldGenerateOperation)
      .flatMap(this::operationImplementationModules)
      .collect(Collectors.toSet());
  }

  private Stream<RustFile> operationImplementationModules(
    final OperationShape operationShape
  ) {
    return operationBindingIndex
      .getBindingShapes(operationShape)
      .stream()
      .flatMap(b ->
        boundOperationImplementationModules(b, operationShape).stream()
      );
  }

  private Set<RustFile> boundOperationImplementationModules(
    final Shape bindingShape,
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
      operationOuterModule(bindingShape, operationShape),
      operationStructureModule(bindingShape, operationShape, inputShape),
      operationStructureModule(bindingShape, operationShape, outputShape),
      operationBuildersModule(bindingShape, operationShape)
    );
  }

  private RustFile operationOuterModule(
    final Shape bindingShape,
    final OperationShape operationShape
  ) {
    Map<String, String> variables = MapUtils.merge(
      serviceVariables(serviceForShape(model, bindingShape)),
      operationVariables(bindingShape, operationShape)
    );
    if (bindingShape.isServiceShape()) {
      StructureShape inputShape = operationIndex
        .getInputShape(operationShape)
        .get();
      if (inputShape.hasTrait(PositionalTrait.class)) {
        // Need to fetch the single member and then convert,
        // since on the Rust side there is still an input structure
        // but not on the Dafny side.
        final MemberShape onlyMember = PositionalTrait.onlyMember(inputShape);
        final String rustValue =
          "input." + toSnakeCase(onlyMember.getMemberName());
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
          fromDafny(outputShape, "inner_result.value()", false, false)
            .toString()
        );
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
        "operationSendBody",
        IOUtils.evalTemplate(
          getClass(),
          "runtimes/rust/operation/outer_send_body.rs",
          variables
        )
      );
    } else {
      variables.put(
        "operationSendBody",
        evalTemplate(
          "$snakeCaseResourceName:L.inner.borrow_mut().$snakeCaseOperationName:L(input)",
          MapUtils.merge(
            variables,
            resourceVariables(bindingShape.asResourceShape().get())
          )
        )
      );
    }

    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/operation/outer.rs",
      variables
    );

    final String snakeCaseOpName = toSnakeCase(operationName(operationShape));
    final Path path = operationsModuleFilePath(bindingShape)
      .resolve(snakeCaseOpName + ".rs");
    return new RustFile(path, TokenTree.of(content));
  }

  private RustFile operationStructureModule(
    final Shape bindingShape,
    final OperationShape operationShape,
    final StructureShape structureShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(serviceForShape(model, bindingShape)),
      operationVariables(bindingShape, operationShape),
      structureVariables(structureShape),
      structureModuleVariables(structureShape)
    );
    final String content = IOUtils.evalTemplate(
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
      serviceVariables(serviceForShape(model, structureShape)),
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
      serviceVariables(serviceForShape(model, bindingShape)),
      operationVariables(bindingShape, operationShape)
    );
    variables.put("accessors", accessors);

    final String content = IOUtils.evalTemplate(
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
    return new RustFile(
      rootPathForShape(service).resolve("error.rs"),
      TokenTree.of(content)
    );
  }

  private RustFile sealedUnhandledErrorModule() {
    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/error/sealed_unhandled.rs",
      Map.of()
    );
    return new RustFile(
      rootPathForShape(service)
        .resolve("error")
        .resolve("sealed_unhandled.rs"),
      TokenTree.of(content)
    );
  }

  protected RustFile conversionsErrorModule() {
    final Map<String, String> variables = serviceVariables();

    final Stream<String> directToDafnyArms = allErrorShapes()
      .map(errorShape ->
        IOUtils.evalTemplate(
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
        IOUtils.evalTemplate(
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
        IOUtils.evalTemplate(
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
        IOUtils.evalTemplate(
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

    final String libraryContent = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/conversions/error_library.rs",
      variables
    );
    final String commonContent = IOUtils.evalTemplate(
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

    final String outerContent = IOUtils.evalTemplate(
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

    final String innerContent = IOUtils.evalTemplate(
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
      serviceVariables(serviceForShape(model, structureShape)),
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
      serviceVariables(serviceForShape(model, unionShape)),
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

  private RustFile resourceConversionModule(final ResourceShape resourceShape) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(serviceForShape(model, resourceShape)),
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
          return IOUtils.evalTemplate(
            getClass(),
            "runtimes/rust/conversions/resource_operation.rs",
            operationVariables
          );
        })
        .collect(Collectors.joining("\n\n"))
    );

    final String content = IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/conversions/resource.rs",
      variables
    );
    final Path path = Path.of(
      "src",
      "conversions",
      "%s.rs".formatted(toSnakeCase(resourceName(resourceShape)))
    );
    return new RustFile(path, TokenTree.of(content));
  }

  @Override
  protected Set<RustFile> boundOperationConversionModules(
    final Shape bindingShape,
    final OperationShape operationShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(serviceForShape(model, bindingShape)),
      operationVariables(bindingShape, operationShape)
    );

    final String operationModuleName = toSnakeCase(
      operationName(operationShape)
    );

    Optional<StructureShape> inputStructure = operationIndex.getInputShape(
      operationShape
    );
    final boolean hasInputStructure =
      inputStructure.isPresent() &&
      !inputStructure.get().hasTrait(PositionalTrait.class);
    Optional<StructureShape> outputStructure = operationIndex.getOutputShape(
      operationShape
    );
    final boolean hasOutputStructure =
      outputStructure.isPresent() &&
      !outputStructure.get().hasTrait(PositionalTrait.class);

    final Set<String> childModules = new HashSet<>();
    if (hasInputStructure) {
      childModules.add(
        "_" + variables.get("snakeCaseSyntheticOperationInputName")
      );
    }
    if (hasOutputStructure) {
      childModules.add(
        "_" + variables.get("snakeCaseSyntheticOperationOutputName")
      );
    }
    final RustFile outerModule = new RustFile(
      rootPathForShape(bindingShape)
        .resolve("conversions")
        .resolve(operationModuleName + ".rs"),
      RustUtils.declarePubModules(childModules.stream())
    );

    Set<RustFile> result = new HashSet<>(Set.of(outerModule));

    if (hasInputStructure) {
      final RustFile requestModule = operationRequestConversionModule(
        bindingShape,
        operationShape
      );
      result.add(requestModule);
    }
    if (hasOutputStructure) {
      final RustFile responseModule = operationResponseConversionModule(
        bindingShape,
        operationShape
      );
      result.add(responseModule);
    }

    return result;
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
      serviceVariables(serviceForShape(model, bindingShape)),
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
      serviceVariables(serviceForShape(model, bindingShape)),
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
            dafny_value: ::std::rc::Rc<
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
    final String content = IOUtils.evalTemplate(
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
        .map(o -> wrappedClientOperationImpl(service, o))
        .collect(Collectors.joining("\n\n"))
    );
    final String content = IOUtils.evalTemplate(
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
      serviceVariables(serviceShape),
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

    return IOUtils.evalTemplate(
      getClass(),
      "runtimes/rust/wrapped/client_operation_impl.part.rs",
      variables
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

  protected HashMap<String, String> serviceVariables() {
    return serviceVariables(service);
  }

  protected ServiceShape serviceForShape(final Model model, final Shape shape) {
    if (shape.isServiceShape()) {
      return (ServiceShape) shape;
    } else {
      final String namespace = shape.getId().getNamespace();
      return ModelUtils.serviceFromNamespace(model, namespace);
    }
  }

  @Override
  protected HashMap<String, String> serviceVariables(
    final ServiceShape serviceShape
  ) {
    final HashMap<String, String> variables = super.serviceVariables(
      serviceShape
    );

    final LocalServiceTrait localServiceTrait = localServiceTrait(serviceShape);
    final String sdkId = localServiceTrait.getSdkId();

    final StructureShape configShape = ModelUtils.getConfigShape(
      model,
      serviceShape
    );
    final String configName = configShape.getId().getName(serviceShape);
    variables.put("sdkId", sdkId);
    variables.put("configName", configName);
    variables.put("snakeCaseConfigName", toSnakeCase(configName));
    variables.put(
      "qualifiedRustServiceErrorType",
      qualifiedRustServiceErrorType(serviceShape)
    );

    return variables;
  }

  @Override
  protected String getRustRootModuleName(final String namespace) {
    return mergedGenerator.isMainNamespace(namespace)
      ? "crate"
      : "crate::deps::" +
      RustUtils.rustModuleForSmithyNamespace(namespace);
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

  protected String qualifiedRustServiceErrorType(
    final ServiceShape serviceShape
  ) {
    return "%s::error::Error".formatted(
        getRustTypesModuleName(serviceShape.getId().getNamespace())
      );
  }

  protected String errorName(final StructureShape errorShape) {
    return errorShape.getId().getName(serviceForShape(model, errorShape));
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
      "%s::%s".formatted(
          qualifiedRustServiceErrorType(serviceForShape(model, errorShape)),
          rustErrorName
        )
    );
    return variables;
  }

  private Map<String, String> dependentServiceErrorVariables(
    final ServiceShape serviceShape,
    final ServiceShape dependentServiceShape
  ) {
    final Map<String, String> variables = new HashMap<>();
    final String rustErrorName = dependentServiceShape.getId().getName() + "Error";
    variables.put(
      "errorName",
      DafnyNameResolver.dafnyBaseModuleName(dependentServiceShape.getId().getNamespace())
    );
    variables.put("rustErrorName", rustErrorName);
    variables.put(
      "rustDependentRootModuleName",
      getRustRootModuleName(dependentServiceShape.getId().getNamespace())
    );
    variables.put(
      "qualifiedRustErrorVariant",
      "%s::%s".formatted(qualifiedRustServiceErrorType(serviceShape), rustErrorName)
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
              ::std::rc::Rc::new(match &%s {
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
        String prefix = topLevelNameForShape(shape);
        if (!isDafnyOption) {
          if (isRustOption) {
            yield TokenTree.of(
              """
              %s::conversions::%s::to_dafny(%s.clone().unwrap())
              """.formatted(prefix, structureShapeName, rustValue)
            );
          } else {
            yield TokenTree.of(
              """
              %s::conversions::%s::to_dafny(%s.clone())
              """.formatted(prefix, structureShapeName, rustValue)
            );
          }
        } else {
          yield TokenTree.of(
            """
            ::std::rc::Rc::new(match &%s {
                Some(x) => crate::_Wrappers_Compile::Option::Some { value: %s::conversions::%s::to_dafny(x.clone()) },
                None => crate::_Wrappers_Compile::Option::None { }
            })
            """.formatted(rustValue, prefix, structureShapeName)
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
              %s::conversions::%s::to_dafny(%s.clone().unwrap())
              """.formatted(prefix, resourceShapeName, rustValue)
            );
          } else {
            yield TokenTree.of(
              """
              %s::conversions::%s::to_dafny(%s.clone())
              """.formatted(prefix, resourceShapeName, rustValue)
            );
          }
        } else {
          yield TokenTree.of(
            """
            ::std::rc::Rc::new(match &%s {
                Some(x) => crate::_Wrappers_Compile::Option::Some { value: %s::conversions::%s::to_dafny(x.clone()) },
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
              %s::conversions::client::to_dafny(%s.clone())
              """.formatted(prefix, rustValue)
            );
          }
        } else {
          yield TokenTree.of(
            """
            ::std::rc::Rc::new(match &%s {
                Some(x) => crate::_Wrappers_Compile::Option::Some { value: %s::conversions::client::to_dafny(x.clone()) },
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
}
