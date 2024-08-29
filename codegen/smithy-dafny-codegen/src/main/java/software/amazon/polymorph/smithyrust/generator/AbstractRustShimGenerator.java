package software.amazon.polymorph.smithyrust.generator;

import static software.amazon.polymorph.utils.IOUtils.evalTemplate;
import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toPascalCase;
import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toSnakeCase;

import java.nio.file.Path;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.utils.IOUtils;
import software.amazon.polymorph.utils.MapUtils;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.knowledge.OperationIndex;
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
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.RequiredTrait;

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
    return service
      .getOperations()
      .stream()
      .sorted()
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
      !isInputOrOutputStructure(structureShape) &&
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
    TokenTree toDafnyOpaqueErrorFunctions = TokenTree.of(
      evalTemplate(
        getClass(),
        "runtimes/rust/conversions/error.rs",
        serviceVariables()
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

  protected RustFile conversionsModule() {
    Stream<String> operationModules = model
      .getOperationShapes()
      .stream()
      .map(operationShape -> toSnakeCase(operationShape.getId().getName()));

    // smithy-dafny generally generates code for all shapes in the same namespace,
    // whereas most smithy code generators generate code for all shapes in the service closure.
    // Here we filter to "normal" structures and unions.
    Stream<String> structureModules = model
      .getStructureShapes()
      .stream()
      .filter(this::shouldGenerateStructForStructure)
      .map(structureShape -> toSnakeCase(structureShape.getId().getName()));
    Stream<String> unionModules = model
      .getUnionShapes()
      .stream()
      .filter(this::shouldGenerateEnumForUnion)
      .map(structureShape -> toSnakeCase(structureShape.getId().getName()));

    Stream<String> enumModules = ModelUtils
      .streamEnumShapes(model, service.getId().getNamespace())
      .map(structureShape -> toSnakeCase(structureShape.getId().getName()));

    TokenTree content = declarePubModules(
      Stream
        .of(
          operationModules,
          structureModules,
          unionModules,
          enumModules,
          Stream.of("error")
        )
        .flatMap(s -> s)
    );

    return new RustFile(Path.of("src", "conversions.rs"), content);
  }

  protected RustFile structureConversionModule(
    final StructureShape structureShape
  ) {
    String snakeCaseName = toSnakeCase(structureName(structureShape));
    Path path = Path.of("src", "conversions", snakeCaseName + ".rs");
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
    final OperationShape operationShape
  ) {
    var toDafnyFunction = operationRequestToDafnyFunction(operationShape);
    var fromDafnyFunction = operationRequestFromDafnyFunction(operationShape);
    var content = TokenTree
      .of(toDafnyFunction, fromDafnyFunction)
      .lineSeparated();

    final String snakeCaseOperationName = toSnakeCase(
      operationName(operationShape)
    );
    final Path path = Path.of(
      "src",
      "conversions",
      snakeCaseOperationName,
      "_%s.rs".formatted(
          toSnakeCase(syntheticOperationInputName(operationShape))
        )
    );
    return new RustFile(path, content);
  }

  protected RustFile operationResponseConversionModule(
    final OperationShape operationShape
  ) {
    var toDafnyFunction = operationResponseToDafnyFunction(operationShape);
    var fromDafnyFunction = operationResponseFromDafnyFunction(operationShape);
    var content = TokenTree
      .of(toDafnyFunction, fromDafnyFunction)
      .lineSeparated();

    final String snakeCaseOperationName = toSnakeCase(
      operationName(operationShape)
    );
    final Path path = Path.of(
      "src",
      "conversions",
      snakeCaseOperationName,
      "_%s.rs".formatted(
          toSnakeCase(syntheticOperationOutputName(operationShape))
        )
    );
    return new RustFile(path, content);
  }

  protected abstract TokenTree operationRequestToDafnyFunction(
    final OperationShape operationShape
  );

  protected abstract TokenTree operationRequestFromDafnyFunction(
    final OperationShape operationShape
  );

  protected abstract TokenTree operationResponseToDafnyFunction(
    final OperationShape operationShape
  );

  protected abstract TokenTree operationResponseFromDafnyFunction(
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
  private TokenTree fromDafny(
    final Shape shape,
    final String dafnyValue,
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
              match &**%s {
                  crate::r#_Wrappers_Compile::Option::Some { value } => Some(
                      crate::conversions::%s::from_dafny(value)
                  ),
                  _ => None,
              }
              """.formatted(dafnyValue, enumShapeName)
            );
          } else {
            TokenTree result = TokenTree.of(
              "crate::conversions::%s::from_dafny(%s)".formatted(
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
            valueToRust = dafnyToRust.formatted(dafnyValue + ".as_ref()");
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
          TokenTree result = TokenTree.of(dafnyValue);
          if (isRustOption) {
            result =
              TokenTree.of(
                TokenTree.of("Some("),
                result,
                TokenTree.of(".clone())")
              );
          }
          yield result;
        }
      }
      case INTEGER -> {
        if (isRustOption) {
          yield TokenTree.of(
            "crate::standard_library_conversions::oint_from_dafny(%s.clone())".formatted(
                dafnyValue
              )
          );
        } else {
          yield TokenTree.of(dafnyValue);
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
          TokenTree result = TokenTree.of(dafnyValue);
          if (isRustOption) {
            result =
              TokenTree.of(
                TokenTree.of("Some("),
                result,
                TokenTree.of(".clone())")
              );
          }
          yield result;
        }
      }
      case DOUBLE -> {
        if (isRustOption) {
          yield TokenTree.of(
            "crate::standard_library_conversions::odouble_from_dafny(%s.clone())".formatted(
                dafnyValue
              )
          );
        } else {
          yield TokenTree.of(
            "crate::standard_library_conversions::double_from_dafny(&%s.clone())".formatted(
                dafnyValue
              )
          );
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
        if (!isDafnyOption) {
          TokenTree result = TokenTree.of(
            """
            ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(%s,
                |e| %s,
            )
            """.formatted(dafnyValue, fromDafny(memberShape, "e", false, false))
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
                            |e| %s,
                        )
                    ),
                _ => None
            }
            """.formatted(dafnyValue, fromDafny(memberShape, "e", false, false))
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
                |k| %s,
                |v| %s,
            )
            """.formatted(
                dafnyValue,
                fromDafny(keyShape, "k", false, false),
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
                            |k| %s,
                            |v| %s,
                        )
                    ),
                _ => None
            }
            """.formatted(
                dafnyValue,
                fromDafny(keyShape, "k", false, false),
                fromDafny(valueShape, "v", false, false)
              )
          );
        }
      }
      case STRUCTURE, UNION -> {
        var structureShapeName = toSnakeCase(shape.getId().getName());
        if (isDafnyOption) {
          yield TokenTree.of(
            """
            match (*%s).as_ref() {
                crate::r#_Wrappers_Compile::Option::Some { value } =>
                    Some(crate::conversions::%s::from_dafny(value.clone())),
                _ => None,
            }
            """.formatted(dafnyValue, structureShapeName)
          );
        } else {
          TokenTree result = TokenTree.of(
            """
            crate::conversions::%s::from_dafny(%s.clone())
            """.formatted(structureShapeName, dafnyValue)
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

  /**
   * @param isRustOption Whether the Rust type is an Option<...> or not.
   *                     Rust's structures avoid Options when not strictly necessary depending on context.
   * @param isDafnyOption Whether the Dafny type is an Option<...> or not.
   *                      Dafny tends to be much more consistent about this.
   *                      We generally trust that Dafny codegen aligns with the constraints,
   *                      and hence is it safe to call unwrap() on Rust options when necessary.
   */
  private TokenTree toDafny(
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
          yield TokenTree.of(rustValue);
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
          yield TokenTree.of(rustValue);
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
          yield TokenTree.of(rustValue);
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
              crate::conversions::%s::to_dafny(&%s)
              """.formatted(structureShapeName, rustValue)
            );
          }
        } else {
          yield TokenTree.of(
            """
            ::std::rc::Rc::new(match &%s {
                Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::conversions::%s::to_dafny(&x) },
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
    return serviceOperationShapes()
      .map(this::operationConversionModules)
      .flatMap(Collection::stream)
      .collect(Collectors.toSet());
  }

  protected abstract Set<RustFile> operationConversionModules(
    final OperationShape operationShape
  );

  protected RustFile enumConversionModule(final EnumShape enumShape) {
    Path path = Path.of(
      "src",
      "conversions",
      toSnakeCase(enumName(enumShape)) + ".rs"
    );

    return new RustFile(
      path,
      TokenTree
        .of(enumToDafnyFunction(enumShape), enumFromDafnyFunction(enumShape))
        .lineSeparated()
    );
  }

  /**
   * Generates values for variables commonly used in service-specific templates.
   */
  protected HashMap<String, String> serviceVariables() {
    final HashMap<String, String> variables = new HashMap<>();
    variables.put("serviceName", service.getId().getName(service));
    variables.put("dafnyModuleName", getDafnyModuleName());
    variables.put("dafnyInternalModuleName", getDafnyInternalModuleName());
    variables.put("dafnyTypesModuleName", getDafnyTypesModuleName());
    variables.put("rustTypesModuleName", getRustTypesModuleName());
    return variables;
  }

  protected String getDafnyModuleName() {
    return service
      .getId()
      .getNamespace()
      .replace(".", "::")
      .toLowerCase(Locale.ROOT);
  }

  protected String getDafnyInternalModuleName() {
    return "%s::internaldafny".formatted(getDafnyModuleName());
  }

  protected String getDafnyTypesModuleName() {
    return "%s::types".formatted(getDafnyInternalModuleName());
  }

  protected abstract String getRustTypesModuleName();

  /**
   * Generates values for variables commonly used in operation-specific templates.
   */
  protected HashMap<String, String> operationVariables(
    final OperationShape operationShape
  ) {
    final String opName = operationName(operationShape);
    final String opInputName = operationInputName(operationShape);
    final String opOutputName = operationOutputName(operationShape);
    final String synOpInputName = syntheticOperationInputName(operationShape);
    final String synOpOutputName = syntheticOperationOutputName(operationShape);
    final String snakeCaseOpName = toSnakeCase(opName);

    final HashMap<String, String> variables = new HashMap<>();
    variables.put("operationName", opName);
    variables.put("operationInputName", opInputName);
    variables.put("operationOutputName", opOutputName);
    variables.put("operationErrorName", operationErrorTypeName(operationShape));
    variables.put("syntheticOperationInputName", synOpInputName);
    variables.put("syntheticOperationOutputName", synOpOutputName);
    variables.put("snakeCaseOperationName", snakeCaseOpName);
    variables.put("snakeCaseOperationInputName", toSnakeCase(opInputName));
    variables.put("snakeCaseOperationOutputName", toSnakeCase(opOutputName));
    variables.put(
      "snakeCaseSyntheticOperationInputName",
      toSnakeCase(synOpInputName)
    );
    variables.put(
      "snakeCaseSyntheticOperationOutputName",
      toSnakeCase(synOpOutputName)
    );
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
        getRustTypesModuleName(),
        rustStructureName(structureShape)
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
    return variables;
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
        getRustTypesModuleName(),
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
}
