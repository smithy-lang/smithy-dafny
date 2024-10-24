package software.amazon.polymorph.smithyrust.generator;

import static software.amazon.polymorph.utils.IOUtils.evalTemplate;
import static software.amazon.polymorph.utils.IOUtils.evalTemplateResource;
import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toPascalCase;
import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toSnakeCase;

import com.google.common.collect.MoreCollectors;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import software.amazon.polymorph.smithyjava.NamespaceHelper;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.polymorph.utils.BoundOperationShape;
import software.amazon.polymorph.utils.IOUtils;
import software.amazon.polymorph.utils.MapUtils;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.OperationBindingIndex;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.knowledge.OperationIndex;
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
import software.amazon.smithy.model.shapes.ToShapeId;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.model.traits.DocumentationTrait;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.RequiredTrait;
import software.amazon.smithy.model.traits.StringTrait;
import software.amazon.smithy.model.traits.UnitTypeTrait;

public abstract class AbstractRustShimGenerator {

  protected MergedServicesGenerator mergedGenerator;

  protected final Model model;
  protected final ServiceShape service;

  protected final OperationIndex operationIndex;
  protected final OperationBindingIndex operationBindingIndex;

  private static final String TOP_LEVEL_MOD_DECLS =
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

  public AbstractRustShimGenerator(
    final MergedServicesGenerator mergedGenerator,
    Model model,
    ServiceShape service
  ) {
    this.mergedGenerator = mergedGenerator;
    this.model = model;
    this.service = service;
    this.operationIndex = new OperationIndex(model);
    this.operationBindingIndex = new OperationBindingIndex(model);
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

  protected Stream<BoundOperationShape> streamAllBoundOperationShapes() {
    return operationBindingIndex
      .getAllBindingShapes()
      .stream()
      .filter(s -> ModelUtils.isInServiceNamespace(s, service))
      .flatMap(s -> operationBindingIndex.getOperations(s).stream());
  }

  protected Stream<StructureShape> allErrorShapes() {
    return model
      .getStructureShapes()
      .stream()
      .filter(s -> s.hasTrait(ErrorTrait.class))
      .filter(o -> ModelUtils.isInServiceNamespace(o, service));
  }

  protected final boolean isInputOrOutputStructure(
    final StructureShape structureShape
  ) {
    return (
      operationIndex.isInputStructure(structureShape) ||
      operationIndex.isOutputStructure(structureShape)
    );
  }

  protected boolean shouldGenerateStructForStructure(
    StructureShape structureShape
  ) {
    return (
      !structureShape.hasTrait(ErrorTrait.class) &&
      !structureShape.hasTrait(ShapeId.from("smithy.api#trait")) &&
      !structureShape.hasTrait(ReferenceTrait.class) &&
      ModelUtils.isInServiceNamespace(structureShape, service)
    );
  }

  protected boolean shouldGenerateTraitForResource(
    ResourceShape resourceShape
  ) {
    return ModelUtils.isInServiceNamespace(resourceShape, service);
  }

  protected final Stream<
    StructureShape
  > streamStructuresToGenerateStructsFor() {
    return model
      .getStructureShapes()
      .stream()
      .filter(this::shouldGenerateStructForStructure)
      .sorted();
  }

  protected final Stream<ResourceShape> streamResourcesToGenerateTraitsFor() {
    return model
      .getStructureShapes()
      .stream()
      .filter(s -> s.hasTrait(ReferenceTrait.class))
      .map(s -> s.expectTrait(ReferenceTrait.class))
      .filter(t -> !t.isService())
      .map(t -> model.expectShape(t.getReferentId(), ResourceShape.class))
      .filter(this::shouldGenerateTraitForResource)
      .sorted();
  }

  protected boolean shouldGenerateEnumForUnion(UnionShape unionShape) {
    return ModelUtils.isInServiceNamespace(unionShape, service);
  }

  protected RustFile conversionsModule() {
    final String namespace = service.getId().getNamespace();
    Stream<String> operationModules = streamAllBoundOperationShapes()
      .map(operationShape ->
        toSnakeCase(operationShape.operationShape().getId().getName())
      );
    Stream<String> resourceModules = streamResourcesToGenerateTraitsFor()
      .map(resourceShape -> toSnakeCase(resourceShape.getId().getName()));

    // smithy-dafny generally generates code for all shapes in the same namespace,
    // whereas most smithy code generators generate code for all shapes in the service closure.
    // Here we filter to "normal" structures and unions.
    Stream<String> structureModules = streamStructuresToGenerateStructsFor()
      .filter(o -> o.getId().getNamespace().equals(namespace))
      .map(structureShape -> toSnakeCase(structureShape.getId().getName()));
    Stream<String> unionModules = model
      .getUnionShapes()
      .stream()
      .filter(this::shouldGenerateEnumForUnion)
      .filter(o -> o.getId().getNamespace().equals(namespace))
      .map(structureShape -> toSnakeCase(structureShape.getId().getName()));

    Stream<String> enumModules = ModelUtils
      .streamEnumShapes(model, service.getId().getNamespace())
      .filter(o -> o.getId().getNamespace().equals(namespace))
      .map(structureShape -> toSnakeCase(structureShape.getId().getName()));

    TokenTree content = RustUtils.declarePubModules(
      Stream
        .of(
          resourceModules,
          operationModules,
          structureModules,
          unionModules,
          enumModules,
          Stream.of("error"),
          Stream.of("client")
        )
        .flatMap(s -> s)
    );

    return new RustFile(
      rootPathForNamespace(namespace).resolve("conversions.rs"),
      content
    );
  }

  protected RustFile structureConversionModule(
    final StructureShape structureShape
  ) {
    String snakeCaseName = toSnakeCase(structureName(structureShape));
    Path path = rootPathForShape(service)
      .resolve("conversions")
      .resolve(snakeCaseName + ".rs");
    return new RustFile(
      path,
      TokenTree.of(
        structureToDafnyFunction(structureShape),
        structureFromDafnyFunction(structureShape)
      )
    );
  }

  protected TokenTree structureToDafnyFunction(
    final StructureShape structureShape
  ) {
    final String template =
      """
      #[allow(dead_code)]
      pub fn to_dafny(
          value: &$rustTypesModuleName:L::$rustStructureName:L,
      ) -> ::std::rc::Rc<crate::r#$dafnyTypesModuleName:L::$structureName:L>{
        ::std::rc::Rc::new(
          crate::r#$dafnyTypesModuleName:L::$structureName:L::$structureName:L {
              $variants:L
          }
        )
      }
      """;
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      structureVariables(structureShape)
    );
    variables.put(
      "variants",
      toDafnyVariantsForStructure(structureShape).toString()
    );

    return TokenTree.of(evalTemplate(template, variables));
  }

  /**
   * Returns whether the Rust struct builder for the given shape is fallible,
   * i.e. its {@code build()} function returns {@code Result<T>}.
   */
  protected abstract boolean isStructureBuilderFallible(
    final StructureShape structureShape
  );

  protected TokenTree structureFromDafnyFunction(
    final StructureShape structureShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      structureVariables(structureShape)
    );
    variables.put(
      "fluentMemberSetters",
      fluentMemberSettersForStructure(structureShape).toString()
    );

    final String unwrapIfNeeded = isStructureBuilderFallible(structureShape)
      ? ".unwrap()"
      : "";
    variables.put("unwrapIfNeeded", unwrapIfNeeded);

    return TokenTree.of(
      evalTemplate(
        """
        #[allow(dead_code)]
        pub fn from_dafny(
            dafny_value: ::std::rc::Rc<
                crate::r#$dafnyTypesModuleName:L::$structureName:L,
            >,
        ) -> $rustTypesModuleName:L::$rustStructureName:L {
            $rustTypesModuleName:L::$rustStructureName:L::builder()
                  $fluentMemberSetters:L
                  .build()
                  $unwrapIfNeeded:L
        }
        """,
        variables
      )
    );
  }

  protected RustFile operationRequestConversionModule(
    final Shape bindingShape,
    final OperationShape operationShape
  ) {
    var toDafnyFunction = operationRequestToDafnyFunction(
      bindingShape,
      operationShape
    );
    var fromDafnyFunction = operationRequestFromDafnyFunction(
      bindingShape,
      operationShape
    );
    var content = TokenTree
      .of(toDafnyFunction, fromDafnyFunction)
      .lineSeparated();

    final String snakeCaseOperationName = toSnakeCase(
      operationName(operationShape)
    );
    final Path path = rootPathForShape(bindingShape)
      .resolve("conversions")
      .resolve(snakeCaseOperationName)
      .resolve(
        "_%s.rs".formatted(
            toSnakeCase(syntheticOperationInputName(operationShape))
          )
      );
    return new RustFile(path, content);
  }

  protected RustFile operationResponseConversionModule(
    final Shape bindingShape,
    final OperationShape operationShape
  ) {
    var toDafnyFunction = operationResponseToDafnyFunction(
      bindingShape,
      operationShape
    );
    var fromDafnyFunction = operationResponseFromDafnyFunction(
      bindingShape,
      operationShape
    );
    var content = TokenTree
      .of(toDafnyFunction, fromDafnyFunction)
      .lineSeparated();

    final String snakeCaseOperationName = toSnakeCase(
      operationName(operationShape)
    );
    final Path path = rootPathForShape(bindingShape)
      .resolve("conversions")
      .resolve(snakeCaseOperationName)
      .resolve(
        "_%s.rs".formatted(
            toSnakeCase(syntheticOperationOutputName(operationShape))
          )
      );
    return new RustFile(path, content);
  }

  protected abstract TokenTree operationRequestToDafnyFunction(
    final Shape bindingShape,
    final OperationShape operationShape
  );

  protected abstract TokenTree operationRequestFromDafnyFunction(
    final Shape bindingShape,
    final OperationShape operationShape
  );

  protected abstract TokenTree operationResponseToDafnyFunction(
    final Shape bindingShape,
    final OperationShape operationShape
  );

  protected abstract TokenTree operationResponseFromDafnyFunction(
    final Shape bindingShape,
    final OperationShape operationShape
  );

  protected TokenTree fluentMemberSettersForStructure(Shape shape) {
    return TokenTree
      .of(
        shape
          .members()
          .stream()
          .map(m ->
            TokenTree.of(
              ".set_" +
              toSnakeCase(m.getMemberName()) +
              "(" +
              fromDafnyForMember(m) +
              ")"
            )
          )
      )
      .lineSeparated();
  }

  protected TokenTree toDafnyVariantsForStructure(
    final StructureShape structureShape
  ) {
    return TokenTree
      .of(
        structureShape
          .members()
          .stream()
          .map(m ->
            TokenTree.of(
              m.getMemberName() +
              ": " +
              toDafnyVariantMember(structureShape, m) +
              ","
            )
          )
      )
      .lineSeparated();
  }

  private TokenTree fromDafnyForMember(MemberShape member) {
    Shape targetShape = model.expectShape(member.getTarget());
    boolean isRequired = member.hasTrait(RequiredTrait.class);
    // isRustOption is always true here because we're using .set_foo(...) fluent builder methods
    // on the Rust side as opposed to just .foo(...), and those all take options
    // even for required members.
    return fromDafny(
      targetShape,
      "dafny_value." + member.getMemberName() + "()",
      true,
      !isRequired
    );
  }

  /**
   * @param isRustOption Whether the Rust type is an Option<...> or not.
   *                     Rust's structures avoid Options when not strictly necessary depending on context.
   * @param isDafnyOption Whether the Dafny type is an Option<...> or not.
   *                      Dafny tends to be much more consistent about this.
   */
  // TODO: There is obviously a lot of duplication here that should be easy to clean up.
  // TODO: Some cases do not handle all combinations of isRustOption and isDafnyOption.
  protected TokenTree fromDafny(
    final Shape originalShape,
    final String dafnyValue,
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
              match &**%s {
                  crate::r#_Wrappers_Compile::Option::Some { value } => Some(
                      %s::conversions::%s::from_dafny(value)
                  ),
                  _ => None,
              }
              """.formatted(dafnyValue, prefix, enumShapeName)
            );
          } else {
            TokenTree result = TokenTree.of(
              "%s::conversions::%s::from_dafny(%s)".formatted(
                  prefix,
                  enumShapeName,
                  dafnyValue
                )
            );
            if (isRustOption) {
              result =
                TokenTree.of(TokenTree.of("Some("), result, TokenTree.of(")"));
            }
            yield result;
          }
        } else if (shape.hasTrait(DafnyUtf8BytesTrait.class)) {
          final String dafnyToRust =
            "::std::string::String::from_utf8(dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(&%s, |b| *b)).unwrap()";
          String valueToRust;
          if (isDafnyOption) {
            valueToRust =
              """
              match %s.as_ref() {
                crate::_Wrappers_Compile::Option::Some { .. } => ::std::option::Option::Some(%s),
                _ => ::std::option::Option::None,
              }""".formatted(
                  dafnyValue,
                  dafnyToRust.formatted(dafnyValue + ".Extract()")
                );
            if (!isRustOption) {
              valueToRust = "(%s).unwrap()".formatted(valueToRust);
            }
          } else {
            valueToRust =
              dafnyToRust.formatted(
                "::std::borrow::Borrow::borrow(%s)".formatted(dafnyValue)
              );
            if (isRustOption) {
              valueToRust = "Some(%s)".formatted(valueToRust);
            }
          }
          yield TokenTree.of(valueToRust);
        } else {
          if (isDafnyOption) {
            yield TokenTree.of(
              "crate::standard_library_conversions::ostring_from_dafny(%s.clone())".formatted(
                  dafnyValue
                )
            );
          } else {
            TokenTree result = TokenTree.of(
              "dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(%s)".formatted(
                  dafnyValue
                )
            );
            if (isRustOption) {
              result =
                TokenTree.of(TokenTree.of("Some("), result, TokenTree.of(")"));
            }
            yield result;
          }
        }
      }
      case BOOLEAN -> {
        if (isDafnyOption) {
          yield TokenTree.of(
            "crate::standard_library_conversions::obool_from_dafny(%s.clone())".formatted(
                dafnyValue
              )
          );
        } else {
          TokenTree result = TokenTree.of(dafnyValue, ".clone()");
          if (isRustOption) {
            result =
              TokenTree.of(TokenTree.of("Some("), result, TokenTree.of(")"));
          }
          yield result;
        }
      }
      case INTEGER -> {
        if (isDafnyOption) {
          yield TokenTree.of(
            "crate::standard_library_conversions::oint_from_dafny(%s.clone())".formatted(
                dafnyValue
              )
          );
        } else {
          TokenTree result = TokenTree.of(dafnyValue, ".clone()");
          if (isRustOption) {
            result =
              TokenTree.of(TokenTree.of("Some("), result, TokenTree.of(")"));
          }
          yield result;
        }
      }
      case LONG -> {
        if (isDafnyOption) {
          yield TokenTree.of(
            "crate::standard_library_conversions::olong_from_dafny(%s.clone())".formatted(
                dafnyValue
              )
          );
        } else {
          TokenTree result = TokenTree.of(dafnyValue, ".clone()");
          if (isRustOption) {
            result =
              TokenTree.of(TokenTree.of("Some("), result, TokenTree.of(")"));
          }
          yield result;
        }
      }
      case DOUBLE -> {
        if (isDafnyOption) {
          yield TokenTree.of(
            "crate::standard_library_conversions::odouble_from_dafny(%s.clone())".formatted(
                dafnyValue
              )
          );
        } else {
          TokenTree result = TokenTree.of(
            "crate::standard_library_conversions::double_from_dafny(&%s.clone())".formatted(
                dafnyValue
              )
          );
          if (isRustOption) {
            result =
              TokenTree.of(TokenTree.of("Some("), result, TokenTree.of(")"));
          }
          yield result;
        }
      }
      case TIMESTAMP -> {
        if (isDafnyOption) {
          yield TokenTree.of(
            "crate::standard_library_conversions::otimestamp_from_dafny(%s.clone())".formatted(
                dafnyValue
              )
          );
        } else if (isRustOption) {
          yield TokenTree.of(
            "Some(crate::standard_library_conversions::timestamp_from_dafny(%s.clone()))".formatted(
                dafnyValue
              )
          );
        } else {
          yield TokenTree.of(
            "crate::standard_library_conversions::timestamp_from_dafny(%s.clone())".formatted(
                dafnyValue
              )
          );
        }
      }
      case BLOB -> {
        if (isDafnyOption) {
          yield TokenTree.of(
            "crate::standard_library_conversions::oblob_from_dafny(%s.clone())".formatted(
                dafnyValue
              )
          );
        } else if (isRustOption) {
          yield TokenTree.of(
            "Some(crate::standard_library_conversions::blob_from_dafny(%s.clone()))".formatted(
                dafnyValue
              )
          );
        } else {
          yield TokenTree.of(
            "crate::standard_library_conversions::blob_from_dafny(%s.clone())".formatted(
                dafnyValue
              )
          );
        }
      }
      case LIST -> {
        ListShape listShape = shape.asListShape().get();
        Shape memberShape = model.expectShape(
          listShape.getMember().getTarget()
        );
        String dafnyElementType = dafnyTypeForShape(memberShape);
        if (!isDafnyOption) {
          TokenTree result = TokenTree.of(
            """
            ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(%s,
                |e: &%s| %s,
            )
            """.formatted(
                dafnyValue,
                dafnyElementType,
                fromDafny(memberShape, "e", false, false)
              )
          );
          if (isRustOption) {
            result =
              TokenTree.of(TokenTree.of("Some("), result, TokenTree.of(")"));
          }
          yield result;
        } else {
          yield TokenTree.of(
            """
            match (*%s).as_ref() {
                crate::r#_Wrappers_Compile::Option::Some { value } =>
                    Some(
                        ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(value,
                            |e: &%s| %s,
                        )
                    ),
                _ => None
            }
            """.formatted(
                dafnyValue,
                dafnyElementType,
                fromDafny(memberShape, "e", false, false)
              )
          );
        }
      }
      case MAP -> {
        MapShape mapShape = shape.asMapShape().get();
        Shape keyShape = model.expectShape(mapShape.getKey().getTarget());
        Shape valueShape = model.expectShape(mapShape.getValue().getTarget());
        if (!isDafnyOption) {
          TokenTree result = TokenTree.of(
            """
            ::dafny_runtime::dafny_runtime_conversions::dafny_map_to_hashmap(&%s,
                |k: &%s| %s,
                |v: &%s| %s,
            )
            """.formatted(
                dafnyValue,
                dafnyTypeForShape(keyShape),
                fromDafny(keyShape, "k", false, false),
                dafnyTypeForShape(valueShape),
                fromDafny(valueShape, "v", false, false)
              )
          );
          if (isRustOption) {
            result =
              TokenTree.of(TokenTree.of("Some("), result, TokenTree.of(")"));
          }
          yield result;
        } else {
          yield TokenTree.of(
            """
            match (*%s).as_ref() {
                crate::r#_Wrappers_Compile::Option::Some { value } =>
                    Some(
                        ::dafny_runtime::dafny_runtime_conversions::dafny_map_to_hashmap(value,
                            |k: &%s| %s,
                            |v: &%s| %s,
                        )
                    ),
                _ => None
            }
            """.formatted(
                dafnyValue,
                dafnyTypeForShape(keyShape),
                fromDafny(keyShape, "k", false, false),
                dafnyTypeForShape(valueShape),
                fromDafny(valueShape, "v", false, false)
              )
          );
        }
      }
      case STRUCTURE, UNION -> {
        var conversionsModule = mergedGenerator
          .generatorForShape(shape)
          .getRustConversionsModuleNameForShape(shape);
        if (isDafnyOption) {
          yield TokenTree.of(
            """
            match (*%s).as_ref() {
                crate::r#_Wrappers_Compile::Option::Some { value } =>
                    Some(%s::from_dafny(value.clone())),
                _ => None,
            }
            """.formatted(dafnyValue, conversionsModule)
          );
        } else {
          TokenTree result = TokenTree.of(
            """
            %s::from_dafny(%s.clone())
            """.formatted(conversionsModule, dafnyValue)
          );
          if (isRustOption) {
            result =
              TokenTree.of(TokenTree.of("Some("), result, TokenTree.of(")"));
          }
          yield result;
        }
      }
      case RESOURCE -> {
        var resourceShapeName = toSnakeCase(shape.getId().getName());
        String prefix = topLevelNameForShape(shape);
        if (isDafnyOption) {
          yield TokenTree.of(
            """
            match (*%s).as_ref() {
                crate::r#_Wrappers_Compile::Option::Some { value } =>
                    Some(%s::conversions::%s::from_dafny(value.clone())),
                _ => None,
            }
            """.formatted(dafnyValue, prefix, resourceShapeName)
          );
        } else {
          TokenTree result = TokenTree.of(
            """
            %s::conversions::%s::from_dafny(%s.clone())
            """.formatted(prefix, resourceShapeName, dafnyValue)
          );
          if (isRustOption) {
            result =
              TokenTree.of(TokenTree.of("Some("), result, TokenTree.of(")"));
          }
          yield result;
        }
      }
      case SERVICE -> {
        String prefix = topLevelNameForShape(shape);
        if (isDafnyOption) {
          yield TokenTree.of(
            """
            match (*%s).as_ref() {
                crate::r#_Wrappers_Compile::Option::Some { value } =>
                    Some(%s::conversions::client::from_dafny(value.clone())),
                _ => None,
            }
            """.formatted(dafnyValue, prefix)
          );
        } else {
          TokenTree result = TokenTree.of(
            """
            %s::conversions::client::from_dafny(%s.clone())
            """.formatted(prefix, dafnyValue)
          );
          if (isRustOption) {
            result =
              TokenTree.of(TokenTree.of("Some("), result, TokenTree.of(")"));
          }
          yield result;
        }
      }
      default -> throw new IllegalArgumentException(
        "Unsupported shape type: %s".formatted(shape.getType())
      );
    };
  }

  private TokenTree toDafnyVariantMember(
    final StructureShape parent,
    final MemberShape member
  ) {
    final Shape targetShape = model.expectShape(member.getTarget());
    final String snakeCaseMemberName = toSnakeCase(member.getMemberName());
    return toDafny(
      targetShape,
      "value." + snakeCaseMemberName,
      !isRustFieldRequired(parent, member),
      !hasRequiredTrait(member)
    );
  }

  protected final boolean hasRequiredTrait(final MemberShape member) {
    return member.hasTrait(RequiredTrait.class);
  }

  protected boolean isRustFieldRequired(
    final StructureShape parent,
    final MemberShape member
  ) {
    // These rules were mostly reverse-engineered from inspection of Rust SDKs,
    // and may not be complete!
    final Shape targetShape = model.expectShape(member.getTarget());
    return (
      hasRequiredTrait(member) &&
      !operationIndex.isOutputStructure(parent) &&
      !operationIndex.isInputStructure(parent) &&
      !targetShape.isStructureShape()
    );
  }

  // TODO: unify overrides of toDafny by figuring out exactly where clones/borrows can be elided
  /**
   * @param isRustOption Whether the Rust type is an Option<...> or not.
   *                     Rust's structures avoid Options when not strictly necessary depending on context.
   * @param isDafnyOption Whether the Dafny type is an Option<...> or not.
   *                      Dafny tends to be much more consistent about this.
   *                      We generally trust that Dafny codegen aligns with the constraints,
   *                      and hence is it safe to call unwrap() on Rust options when necessary.
   */
  protected abstract TokenTree toDafny(
    final Shape shape,
    final String rustValue,
    boolean isRustOption,
    boolean isDafnyOption
  );

  protected TokenTree enumToDafnyFunction(final EnumShape enumShape) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      enumVariables(enumShape)
    );
    var branches = enumShape
      .getEnumValues()
      .keySet()
      .stream()
      .map(memberName ->
        evalTemplate(
          "$rustTypesModuleName:L::$rustEnumName:L::$rustEnumMemberName:L => crate::r#$dafnyTypesModuleName:L::$enumName:L::$dafnyEnumMemberName:L {},",
          MapUtils.merge(variables, enumMemberVariables(memberName))
        )
      )
      .collect(Collectors.joining("\n"));
    variables.put("branches", branches);

    // TODO: This should not be a panic, but the Dafny image of the enum shape doesn't have an Unknown variant of any kind,
    // so there's no way to succeed.
    // See https://github.com/smithy-lang/smithy-dafny/issues/476.
    // This could be handled more cleanly if conversion functions returned Results,
    // but that would be a large and disruptive change to the overall code flow.
    return TokenTree.of(
      evalTemplate(
        """
        #[allow(dead_code)]

        pub fn to_dafny(
            value: $rustTypesModuleName:L::$rustEnumName:L,
        ) -> ::std::rc::Rc<crate::r#$dafnyTypesModuleName:L::$enumName:L>{
            ::std::rc::Rc::new(match value {
                $branches:L
                _ => panic!("Unknown enum variant: {}", value),
            })
        }
        """,
        variables
      )
    );
  }

  protected TokenTree enumFromDafnyFunction(final EnumShape enumShape) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      enumVariables(enumShape)
    );

    var branches = enumShape
      .getEnumValues()
      .keySet()
      .stream()
      .map(memberName ->
        evalTemplate(
          "crate::r#$dafnyTypesModuleName:L::$enumName:L::$dafnyEnumMemberName:L {} => $rustTypesModuleName:L::$rustEnumName:L::$rustEnumMemberName:L,",
          MapUtils.merge(variables, enumMemberVariables(memberName))
        )
      )
      .collect(Collectors.joining("\n"));
    variables.put("branches", branches);

    return TokenTree.of(
      evalTemplate(
        """
        #[allow(dead_code)]
        pub fn from_dafny(
            dafny_value: &crate::r#$dafnyTypesModuleName:L::$enumName:L,
        ) -> $rustTypesModuleName:L::$rustEnumName:L {
            match dafny_value {
                $branches:L
            }
        }
        """,
        variables
      )
    );
  }

  protected Set<RustFile> allOperationConversionModules() {
    return streamAllBoundOperationShapes()
      .map(this::boundOperationConversionModules)
      .flatMap(Collection::stream)
      .collect(Collectors.toSet());
  }

  protected Set<RustFile> boundOperationConversionModules(
    final BoundOperationShape boundOperationShape
  ) {
    final Shape bindingShape = boundOperationShape.bindingShape();
    final OperationShape operationShape = boundOperationShape.operationShape();

    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
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
      !inputStructure.get().hasTrait(PositionalTrait.class) &&
      !inputStructure.get().hasTrait(UnitTypeTrait.class);
    Optional<StructureShape> outputStructure = operationIndex.getOutputShape(
      operationShape
    );
    final boolean hasOutputStructure =
      outputStructure.isPresent() &&
      !outputStructure.get().hasTrait(PositionalTrait.class) &&
      !outputStructure.get().hasTrait(UnitTypeTrait.class);

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
      TokenTree
        .of(
          operationErrorConversionFunctions(boundOperationShape),
          RustUtils.declarePubModules(childModules.stream())
        )
        .lineSeparated()
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

  protected TokenTree operationErrorConversionFunctions(
    final BoundOperationShape boundOperationShape
  ) {
    // By default none necessary, but SDKs need them
    return TokenTree.empty();
  }

  protected RustFile enumConversionModule(final EnumShape enumShape) {
    Path path = rootPathForShape(service)
      .resolve("conversions")
      .resolve(toSnakeCase(enumName(enumShape)) + ".rs");

    return new RustFile(
      path,
      TokenTree
        .of(enumToDafnyFunction(enumShape), enumFromDafnyFunction(enumShape))
        .lineSeparated()
    );
  }

  protected RustFile unionConversionModule(final UnionShape unionShape) {
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
          evalTemplate(
            """
            $qualifiedRustUnionName:L::$rustUnionMemberName:L(x) =>
                crate::r#$dafnyTypesModuleName:L::$dafnyUnionName:L::$unionMemberName:L {
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
          evalTemplate(
            """
            crate::r#$dafnyTypesModuleName:L::$dafnyUnionName:L::$unionMemberName:L {
                $dafnyUnionMemberName:L: x @ _,
            } => $qualifiedRustUnionName:L::$rustUnionMemberName:L($innerFromDafny:L),
            """,
            memberVariables
          )
        )
        .collect(Collectors.joining("\n"))
    );

    final String content = evalTemplateResource(
      getClass(),
      "runtimes/rust/conversions/union.rs",
      variables
    );
    final Path path = rootPathForShape(service)
      .resolve("conversions")
      .resolve("%s.rs".formatted(toSnakeCase(unionName(unionShape))));
    return new RustFile(path, TokenTree.of(content));
  }

  /**
   * Generates values for variables commonly used in service-specific templates.
   */
  protected HashMap<String, String> serviceVariables() {
    final String namespace = service.getId().getNamespace();
    final HashMap<String, String> variables = new HashMap<>();
    variables.put("sdkId", getSdkId());
    variables.put("serviceName", service.getId().getName(service));
    variables.put("rustClientType", qualifiedRustServiceType(service));
    variables.put("dafnyModuleName", getDafnyModuleName(namespace));
    variables.put("rustStructureComment", docFromShape(service));
    variables.put(
      "dafnyInternalModuleName",
      getDafnyInternalModuleName(namespace)
    );
    variables.put("dafnyTypesModuleName", getDafnyTypesModuleName(namespace));
    variables.put("rustRootModuleName", getRustRootModuleName(namespace));
    variables.put("rustTypesModuleName", getRustTypesModuleName());
    variables.put(
      "rustConversionsModuleName",
      getRustConversionsModuleName(namespace)
    );
    return variables;
  }

  protected String getDafnyModuleName(final String namespace) {
    String dafnyExternName = NamespaceHelper.standardize(namespace);
    return dafnyExternName.replace(".", "::").toLowerCase(Locale.ROOT);
  }

  protected String getDafnyInternalModuleName(final String namespace) {
    return "%s::internaldafny".formatted(getDafnyModuleName(namespace));
  }

  protected String getDafnyTypesModuleName(final String namespace) {
    return "%s::types".formatted(getDafnyInternalModuleName(namespace));
  }

  protected String getRustRootModuleName(final String namespace) {
    return mergedGenerator.isMainNamespace(namespace)
      ? "crate"
      : "crate::deps::" + RustUtils.rustModuleForSmithyNamespace(namespace);
  }

  protected abstract String getRustTypesModuleName();

  protected String getRustConversionsModuleName(final String namespace) {
    return getRustRootModuleName(namespace) + "::conversions";
  }

  protected String getRustConversionsModuleNameForShape(final Shape shape) {
    final String namespace = shape.getId().getNamespace();
    return switch (shape.getType()) {
      case STRUCTURE, UNION, ENUM -> getRustConversionsModuleName(namespace) +
      "::" +
      toSnakeCase(shape.getId().getName());
      default -> "crate::standard_library_conversions";
    };
  }

  /**
   * Generates values for variables commonly used in operation-specific templates.
   */
  protected HashMap<String, String> operationVariables(
    final Shape bindingShape,
    final OperationShape operationShape
  ) {
    final String opName = operationName(operationShape);
    final String opInputName = operationInputName(operationShape);
    final String opOutputName = operationOutputName(operationShape);
    final String opErrorName = operationErrorTypeName(operationShape);
    final String synOpInputName = syntheticOperationInputName(operationShape);
    final String synOpOutputName = syntheticOperationOutputName(operationShape);

    final HashMap<String, String> variables = new HashMap<>();
    variables.put("rustRootModuleName", topLevelNameForShape(bindingShape));
    variables.put("operationName", opName);
    variables.put("operationInputName", opInputName);
    variables.put("operationOutputName", opOutputName);
    variables.put("operationErrorName", opErrorName);
    variables.put("syntheticOperationInputName", synOpInputName);
    variables.put("syntheticOperationOutputName", synOpOutputName);
    variables.put("snakeCaseOperationName", toSnakeCase(opName));
    variables.put("snakeCaseOperationInputName", toSnakeCase(opInputName));
    variables.put("snakeCaseOperationOutputName", toSnakeCase(opOutputName));
    variables.put("rustOperationComment", docFromShapeEmpty(operationShape));
    variables.put(
      "snakeCaseSyntheticOperationInputName",
      toSnakeCase(synOpInputName)
    );
    variables.put(
      "snakeCaseSyntheticOperationOutputName",
      toSnakeCase(synOpOutputName)
    );
    variables.put("pascalCaseOperationName", toPascalCase(opName));
    variables.put("pascalCaseOperationInputName", toPascalCase(opInputName));
    variables.put("pascalCaseOperationOutputName", toPascalCase(opOutputName));
    variables.put("pascalCaseOperationErrorName", toPascalCase(opErrorName));

    if (bindingShape.isServiceShape()) {
      variables.put("operationTargetName", "client");
      variables.put(
        "operationTargetType",
        qualifiedRustServiceType((ServiceShape) bindingShape)
      );
    } else {
      Map<String, String> resourceVariables = resourceVariables(
        bindingShape.asResourceShape().get()
      );
      variables.put(
        "operationTargetName",
        resourceVariables.get("snakeCaseResourceName")
      );
      variables.put(
        "operationTargetType",
        evalTemplate(
          "$rustRootModuleName:L::types::$snakeCaseResourceName:L::$rustResourceName:LRef",
          MapUtils.merge(variables, resourceVariables)
        )
      );
    }

    final StructureShape inputShape = operationIndex
      .getInputShape(operationShape)
      .get();
    variables.put(
      "operationInputType",
      evalTemplate(
        "$rustRootModuleName:L::operation::$snakeCaseOperationName:L::$pascalCaseOperationInputName:L",
        variables
      )
    );
    if (inputShape.hasTrait(PositionalTrait.class)) {
      Shape resolvedInputShape = model.expectShape(
        ModelUtils.resolveShape(inputShape, model).resolvedId()
      );
      variables.put(
        "operationDafnyInputType",
        dafnyTypeForShape(resolvedInputShape)
      );
    } else {
      Map<String, String> inputShapeVariables = structureVariables(inputShape);
      variables.put(
        "operationDafnyInputType",
        evalTemplate(
          "&::std::rc::Rc<crate::$dafnyTypesModuleName:L::$structureName:L>",
          inputShapeVariables
        )
      );
    }

    final StructureShape outputShape = operationIndex
      .getOutputShape(operationShape)
      .get();
    if (
      outputShape.hasTrait(PositionalTrait.class) ||
      outputShape.hasTrait(UnitTypeTrait.class)
    ) {
      variables.put("operationOutputType", rustTypeForShape(outputShape));
      variables.put("operationDafnyOutputType", dafnyTypeForShape(outputShape));
    } else {
      variables.put(
        "operationOutputType",
        evalTemplate(
          "$rustRootModuleName:L::operation::$snakeCaseOperationName:L::$pascalCaseOperationOutputName:L",
          variables
        )
      );
      Map<String, String> outputShapeVariables = structureVariables(
        outputShape
      );
      variables.put(
        "operationDafnyOutputType",
        evalTemplate(
          "::std::rc::Rc<crate::r#$dafnyTypesModuleName:L::$structureName:L>",
          outputShapeVariables
        )
      );
    }

    return variables;
  }

  protected String operationName(final OperationShape operationShape) {
    return operationShape.getId().getName(service);
  }

  protected String operationInputName(final OperationShape operationShape) {
    return operationShape.getInputShape().getName(service);
  }

  protected String operationOutputName(final OperationShape operationShape) {
    return operationShape.getOutputShape().getName(service);
  }

  protected abstract String syntheticOperationInputName(
    final OperationShape operationShape
  );

  protected abstract String syntheticOperationOutputName(
    final OperationShape operationShape
  );

  protected String operationErrorTypeName(final OperationShape operationShape) {
    return "%sError".formatted(operationName(operationShape));
  }

  protected String structureName(final StructureShape structureShape) {
    return structureShape.getId().getName(service);
  }

  protected String rustStructureName(final StructureShape structureShape) {
    return toPascalCase(structureName(structureShape));
  }

  protected String qualifiedRustStructureType(
    final StructureShape structureShape
  ) {
    return "%s::%s".formatted(
        mergedGenerator
          .generatorForShape(structureShape)
          .getRustTypesModuleName(),
        rustStructureName(structureShape)
      );
  }

  protected String topLevelNameForShape(final ToShapeId toShapeId) {
    final ShapeId shapeId = toShapeId.toShapeId();
    if (mergedGenerator.isMainNamespace(shapeId.getNamespace())) {
      return "crate";
    } else {
      return (
        "crate::deps::" +
        RustUtils.rustModuleForSmithyNamespace(shapeId.getNamespace())
      );
    }
  }

  public Path rootPathForNamespace(final String namespace) {
    if (mergedGenerator.isMainNamespace(namespace)) {
      return Path.of("src");
    } else {
      return Path.of(
        "src",
        "deps",
        RustUtils.rustModuleForSmithyNamespace(namespace)
      );
    }
  }

  public Path rootPathForShape(final ToShapeId toShapeId) {
    return rootPathForNamespace(toShapeId.toShapeId().getNamespace());
  }

  protected String qualifiedRustServiceType(final ServiceShape serviceShape) {
    return topLevelNameForShape(serviceShape) + "::client::Client";
  }

  protected String qualifiedRustResourceType(
    final ResourceShape resourceShape
  ) {
    return evalTemplate(
      topLevelNameForShape(resourceShape) +
      "::types::$snakeCaseResourceName:L::$rustResourceName:LRef",
      resourceVariables(resourceShape)
    );
  }

  protected HashMap<String, String> structureVariables(
    final StructureShape structureShape
  ) {
    final HashMap<String, String> variables = new HashMap<>();
    final String structureName = structureName(structureShape);
    variables.put("structureName", structureName);
    variables.put("snakeCaseStructureName", toSnakeCase(structureName));
    variables.put("rustStructureName", rustStructureName(structureShape));
    variables.put("rustStructureComment", docFromShape(structureShape));
    // TODO: Risky...
    variables.put(
      "dafnyTypesModuleName",
      getDafnyTypesModuleName(structureShape.getId().getNamespace())
    );
    return variables;
  }

  protected HashMap<String, String> resourceVariables(
    final ResourceShape resourceShape
  ) {
    final HashMap<String, String> variables = new HashMap<>();
    final String resourceName = resourceName(resourceShape);
    variables.put("resourceName", resourceName);
    variables.put("snakeCaseResourceName", toSnakeCase(resourceName));
    variables.put("rustResourceName", rustResourceTraitName(resourceShape));
    variables.put("dafnyResourceName", dafnyResourceTraitName(resourceShape));
    variables.put("rustResourceComment", docFromShape(resourceShape));
    return variables;
  }

  protected String docFromShape(Shape shape) {
    Optional<String> maybeDoc = ModelUtils.getDocumentationOrJavadoc(shape);
    if (maybeDoc.isPresent()) {
      return "/// " + String.join("\n/// ", maybeDoc.get().split("\\r?\\n"));
    } else {
      return "#[allow(missing_docs)]";
    }
  }

  protected String docFromShapeEmpty(Shape shape) {
    Optional<String> maybeDoc = ModelUtils.getDocumentationOrJavadoc(shape);
    if (maybeDoc.isPresent()) {
      return (
        "///\n/// " + String.join("\n/// ", maybeDoc.get().split("\\r?\\n"))
      );
    } else {
      return "///";
    }
  }

  /**
   * Generates values for variables commonly used in templates specific to standard structures
   * (e.g. not operation-related or {@code @error} structures).
   */
  protected HashMap<String, String> standardStructureVariables(
    final StructureShape structureShape
  ) {
    final HashMap<String, String> variables = structureVariables(
      structureShape
    );
    variables.put(
      "qualifiedRustStructureType",
      qualifiedRustStructureType(structureShape)
    );
    variables.put("rustStructureComment", docFromShape(structureShape));
    return variables;
  }

  protected String enumName(final EnumShape enumShape) {
    return enumShape.getId().getName(service);
  }

  protected String rustEnumName(final EnumShape enumShape) {
    return toPascalCase(enumName(enumShape));
  }

  protected String qualifiedRustEnumType(final EnumShape enumShape) {
    return "%s::%s".formatted(
        mergedGenerator.generatorForShape(enumShape).getRustTypesModuleName(),
        rustEnumName(enumShape)
      );
  }

  protected HashMap<String, String> enumVariables(final EnumShape enumShape) {
    final HashMap<String, String> variables = new HashMap<>();
    final String enumName = enumName(enumShape);
    variables.put("enumName", enumName);
    variables.put("snakeCaseEnumName", toSnakeCase(enumName));
    variables.put("rustEnumName", rustEnumName(enumShape));
    variables.put("qualifiedRustEnumType", qualifiedRustEnumType(enumShape));
    variables.put("rustEnumComment", docFromShape(enumShape));
    return variables;
  }

  protected String rustEnumMemberName(final String memberName) {
    return toPascalCase(memberName);
  }

  protected String dafnyEnumMemberName(final String memberName) {
    return memberName;
  }

  protected HashMap<String, String> enumMemberVariables(
    final String memberName
  ) {
    final HashMap<String, String> variables = new HashMap<>();
    variables.put("enumMemberName", memberName);
    variables.put("dafnyEnumMemberName", dafnyEnumMemberName(memberName));
    variables.put("rustEnumMemberName", rustEnumMemberName(memberName));
    return variables;
  }

  protected String resourceName(final ResourceShape resource) {
    return resource.getId().getName(service);
  }

  protected String rustResourceTraitName(final ResourceShape resource) {
    return toPascalCase(resourceName(resource));
  }

  protected String dafnyResourceTraitName(final ResourceShape resource) {
    return "I" + resourceName(resource);
  }

  protected String unionName(final UnionShape unionShape) {
    return unionShape.getId().getName(service);
  }

  protected String rustUnionName(final UnionShape unionShape) {
    return toPascalCase(unionName(unionShape));
  }

  protected String qualifiedRustUnionName(final UnionShape unionShape) {
    return "%s::%s".formatted(
        mergedGenerator.generatorForShape(unionShape).getRustTypesModuleName(),
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
    variables.put("rustUnionComment", docFromShape(unionShape));
    return variables;
  }

  protected String unionMemberName(final MemberShape memberShape) {
    return memberShape.getMemberName();
  }

  protected String rustUnionMemberName(final MemberShape memberShape) {
    return toPascalCase(unionMemberName(memberShape));
  }

  protected String dafnyUnionMemberName(final MemberShape memberShape) {
    return DafnyNameResolver.escapeName(unionMemberName(memberShape));
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

  /**
   * Generates values for variables commonly used in structure-member-specific templates.
   */
  protected HashMap<String, String> structureMemberVariables(
    final MemberShape memberShape
  ) {
    final HashMap<String, String> variables = new HashMap<>();
    final String memberName = memberShape.getMemberName();
    final Shape targetShape = model.expectShape(memberShape.getTarget());
    variables.put("memberName", memberName);
    variables.put("fieldName", toSnakeCase(memberName));
    variables.put("fieldType", mergedGeneratorRustTypeForShape(targetShape));
    return variables;
  }

  protected String qualifiedRustServiceErrorType() {
    return "%s::error::Error".formatted(getRustTypesModuleName());
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
      "%s::%s".formatted(qualifiedRustServiceErrorType(), rustErrorName)
    );
    variables.put(
      "qualifiedRustServiceErrorType",
      qualifiedRustServiceErrorType()
    );

    // This is where smithy-dafny's assumption about error shapes shows up
    var messageMember = errorShape
      .members()
      .stream()
      .filter(m -> m.getMemberName().equalsIgnoreCase("message"))
      .collect(MoreCollectors.onlyElement());
    variables.put("errorMessageMemberName", messageMember.getMemberName());

    return variables;
  }

  protected String mergedGeneratorRustTypeForShape(final Shape shape) {
    AbstractRustShimGenerator forShape = mergedGenerator.generatorForShape(
      shape
    );
    return forShape != null
      ? forShape.rustTypeForShape(shape)
      : rustTypeForShape(shape);
  }

  protected String rustTypeForShape(final Shape originalShape) {
    // First handle indirection like @reference
    final ModelUtils.ResolvedShapeId resolvedShapeId = ModelUtils.resolveShape(
      originalShape,
      model
    );
    final Shape shape = model.expectShape(resolvedShapeId.resolvedId());

    if (shape.hasTrait(UnitTypeTrait.class)) {
      return "()";
    }

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
      case STRUCTURE -> qualifiedRustStructureType((StructureShape) shape);
      case UNION -> qualifiedRustUnionName((UnionShape) shape);
      case RESOURCE -> qualifiedRustResourceType((ResourceShape) shape);
      case SERVICE -> qualifiedRustServiceType((ServiceShape) shape);
      default -> throw new UnsupportedOperationException(
        "Unsupported shape type: " + shape.getType()
      );
    };
  }

  protected String dafnyTypeForShape(final Shape originalShape) {
    // First handle indirection like @reference and @positional
    final ModelUtils.ResolvedShapeId resolvedShapeId = ModelUtils.resolveShape(
      originalShape,
      model
    );
    final Shape shape = model.expectShape(resolvedShapeId.resolvedId());

    if (shape.hasTrait(UnitTypeTrait.class)) {
      return "()";
    }

    return switch (shape.getType()) {
      case BOOLEAN -> "::std::primitive::bool";
      // integral
      case BYTE -> "::std::primitive::i8";
      case SHORT -> "::std::primitive::i16";
      case INTEGER -> "::std::primitive::i32";
      case LONG -> "::std::primitive::i64";
      // floats
      case FLOAT -> "::dafny_runtime::Sequence<u8>";
      case DOUBLE -> "::dafny_runtime::Sequence<u8>";
      // special numerics
      case BIG_INTEGER -> "::num::bigint::BigInt";
      case BIG_DECIMAL -> "::num::rational::BigRational";
      // special collections
      case BLOB -> "::dafny_runtime::dafny_runtime_conversions::DafnySequence<u8>";
      case STRING -> {
        //noinspection deprecation
        if (shape.hasTrait(EnumTrait.class)) {
          EnumShape enumShape = ModelUtils.stringToEnumShape(
            shape.asStringShape().orElseThrow()
          );
          yield "::std::rc::Rc<crate::" +
          getDafnyTypesModuleName(shape.getId().getNamespace()) +
          "::" +
          enumName(enumShape) +
          ">";
        }
        if (shape.hasTrait(DafnyUtf8BytesTrait.class)) {
          yield "::dafny_runtime::dafny_runtime_conversions::DafnySequence<u8>";
        }
        yield "::dafny_runtime::dafny_runtime_conversions::DafnySequence<::dafny_runtime::dafny_runtime_conversions::DafnyCharUTF16>";
      }
      case ENUM -> "::std::rc::Rc<crate::" +
      getDafnyTypesModuleName(shape.getId().getNamespace()) +
      "::" +
      enumName((EnumShape) shape) +
      ">";
      // other simple shapes
      case TIMESTAMP -> "::dafny_runtime::dafny_runtime_conversions::DafnySequence<::dafny_runtime::dafny_runtime_conversions::DafnyCharUTF16>";
      // aggregates
      case LIST -> {
        final ListShape listShape = (ListShape) shape;
        final String memberType = dafnyTypeForShape(
          model.expectShape(listShape.getMember().getTarget())
        );
        yield "::dafny_runtime::dafny_runtime_conversions::DafnySequence<%s>".formatted(
            memberType
          );
      }
      case MAP -> {
        final MapShape mapShape = (MapShape) shape;
        final String keyType = dafnyTypeForShape(
          model.expectShape(mapShape.getKey().getTarget())
        );
        final String valueType = dafnyTypeForShape(
          model.expectShape(mapShape.getValue().getTarget())
        );
        yield "::dafny_runtime::dafny_runtime_conversions::DafnyMap<%s, %s>".formatted(
            keyType,
            valueType
          );
      }
      case STRUCTURE -> "::std::rc::Rc<crate::r#" +
      getDafnyTypesModuleName(shape.getId().getNamespace()) +
      "::" +
      structureName((StructureShape) shape) +
      ">";
      case UNION -> "::std::rc::Rc<crate::r#" +
      getDafnyTypesModuleName(shape.getId().getNamespace()) +
      "::" +
      unionName((UnionShape) shape) +
      ">";
      case RESOURCE -> "::dafny_runtime::Object<dyn crate::r#" +
      getDafnyTypesModuleName(shape.getId().getNamespace()) +
      "::I" +
      resourceName((ResourceShape) shape) +
      ">";
      case SERVICE -> {
        ServiceShape service = (ServiceShape) shape;
        yield "::dafny_runtime::Object<dyn crate::r#" +
        getDafnyTypesModuleName(shape.getId().getNamespace()) +
        "::I" +
        mergedGenerator.generatorForShape(service).getSdkId() +
        "Client>";
      }
      default -> throw new UnsupportedOperationException(
        "Unsupported shape type: " + shape.getType()
      );
    };
  }

  public abstract TokenTree topLevelModuleDeclarations();

  public RustFile depTopLevelModule() {
    final String rustModule = RustUtils.rustModuleForSmithyNamespace(
      service.getId().getNamespace()
    );
    return new RustFile(
      Path.of("src", "deps", rustModule + ".rs"),
      topLevelModuleDeclarations()
    );
  }

  protected abstract String getSdkId();

  protected ServiceShape serviceForShape(final Model model, final Shape shape) {
    if (shape.isServiceShape()) {
      return (ServiceShape) shape;
    } else {
      final String namespace = shape.getId().getNamespace();
      return ModelUtils.serviceFromNamespace(model, namespace);
    }
  }
}
