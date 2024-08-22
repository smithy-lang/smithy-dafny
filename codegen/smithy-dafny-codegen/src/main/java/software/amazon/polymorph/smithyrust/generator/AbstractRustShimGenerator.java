package software.amazon.polymorph.smithyrust.generator;

import software.amazon.awssdk.codegen.model.rules.endpoints.OperationInput;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.utils.IOUtils;
import software.amazon.polymorph.utils.MapUtils;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.knowledge.OperationIndex;
import software.amazon.smithy.model.shapes.ListShape;
import software.amazon.smithy.model.shapes.MapShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.model.traits.EnumDefinition;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.RequiredTrait;

import java.nio.file.Path;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static software.amazon.polymorph.utils.IOUtils.evalTemplate;
import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toPascalCase;
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
    TokenTree toDafnyOpaqueErrorFunctions = TokenTree.of(
      evalTemplate(getClass(), "runtimes/rust/conversions/error.rs", dafnyModuleVariables())
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

  protected Map<String, String> dafnyModuleVariables() {
    final Map<String, String> stringStringMap = new HashMap<>();
    stringStringMap.put("dafnyModuleName", getDafnyModuleName());
    stringStringMap.put("dafnyInternalModuleName", getDafnyInternalModuleName());
    stringStringMap.put("dafnyTypesModuleName", getDafnyTypesModuleName());
    return stringStringMap;
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

    Stream<String> enumModules = model
      .getStringShapesWithTrait(EnumTrait.class)
      .stream()
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

  protected RustFile operationRequestConversionModule(
    final OperationShape operationShape
  ) {
    var toDafnyFunction = operationRequestToDafnyFunction(operationShape);
    var fromDafnyFunction = operationRequestFromDafnyFunction(operationShape);
    var content = TokenTree.of(toDafnyFunction, fromDafnyFunction).lineSeparated();

    final Path path = Path.of(
      "src",
      "conversions",
      toSnakeCase(operationName(operationShape)),
      "_%s.rs".formatted(toSnakeCase(operationInputName(operationShape)))
    );
    return new RustFile(path, content);
  }

  protected RustFile operationResponseConversionModule(
    final OperationShape operationShape
  ) {
    var toDafnyFunction = operationResponseToDafnyFunction(operationShape);
    var fromDafnyFunction = operationResponseFromDafnyFunction(operationShape);
    var content = TokenTree.of(toDafnyFunction, fromDafnyFunction).lineSeparated();

    final Path path = Path.of(
      "src",
      "conversions",
      toSnakeCase(operationName(operationShape)),
      "_%s.rs".formatted(toSnakeCase(operationOutputName(operationShape)))
    );
    return new RustFile(path, content);
  }

  protected abstract TokenTree operationRequestToDafnyFunction(final OperationShape operationShape);

  protected abstract TokenTree operationRequestFromDafnyFunction(final OperationShape operationShape);

  protected abstract TokenTree operationResponseToDafnyFunction(final OperationShape operationShape);

  protected abstract TokenTree operationResponseFromDafnyFunction(final OperationShape operationShape);

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

  protected TokenTree toDafnyVariantsForStructure(Shape shape) {
    return TokenTree
      .of(
        shape
          .members()
          .stream()
          .map(m ->
            TokenTree.of(
              m.getMemberName() +
              ": " +
              toDafnyVariantMemberForOperationRequest(shape, m) +
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
      case STRING -> {
        if (shape.hasTrait(EnumTrait.class)) {
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

  private TokenTree toDafnyVariantMemberForOperationRequest(
    Shape parent,
    MemberShape member
  ) {
    Shape targetShape = model.expectShape(member.getTarget());
    String snakeCaseMemberName = toSnakeCase(member.getMemberName());
    boolean isRequired = member.hasTrait(RequiredTrait.class);
    // These rules were mostly reverse-engineered from inspection of Rust SDKs,
    // and may not be complete!
    boolean isRustRequired =
      (isRequired &&
        !operationIndex.isOutputStructure(parent) &&
        !operationIndex.isInputStructure(parent) &&
        !targetShape.isStructureShape()) ||
      (operationIndex.isOutputStructure(parent) &&
        targetShape.isIntegerShape());
    return toDafny(
      targetShape,
      "value." + snakeCaseMemberName,
      !isRustRequired,
      !isRequired
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
      case STRING -> {
        if (shape.hasTrait(EnumTrait.class)) {
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

  protected TokenTree enumToDafnyFunction(final Shape enumShape) {
    String enumName = enumShape.getId().getName();
    String rustEnumName = toPascalCase(enumName);
    String sdkId = service
      .expectTrait(ServiceTrait.class)
      .getSdkId()
      .toLowerCase();
    String dafnyTypesModuleName = getDafnyTypesModuleName();
    Map<String, String> variables = Map.of(
      "sdkCrate",
      "aws_sdk_" + sdkId,
      "enumName",
      enumName,
      "rustEnumName",
      rustEnumName,
      "dafnyTypesModuleName",
      dafnyTypesModuleName
    );

    String sdkTypeName = evalTemplate(
      "$sdkCrate:L::types::$rustEnumName:L",
      variables
    );

    var prelude = TokenTree.of(
      evalTemplate(
        """
        #[allow(dead_code)]

        pub fn to_dafny(
            value: $sdkCrate:L::types::$rustEnumName:L,
        ) -> ::std::rc::Rc<crate::r#$dafnyTypesModuleName:L::$enumName:L>{
            ::std::rc::Rc::new(match value {

        """,
        variables
      )
    );

    var branches = TokenTree
      .of(
        enumShape
          .expectTrait(EnumTrait.class)
          .getValues()
          .stream()
          .map(e ->
            TokenTree.of(
              sdkTypeName +
              "::" +
              rustEnumName(e) +
              " => crate::r#" +
              dafnyTypesModuleName +
              "::" +
              enumName +
              "::" +
              dafnyEnumName(e) +
              " {},"
            )
          )
      )
      .lineSeparated();
    // TODO: This should not be a panic, but the Dafny image of the enum shape doesn't have an Unknown variant of any kind,
    // so there's no way to succeed.
    // See https://github.com/smithy-lang/smithy-dafny/issues/476.
    // This could be handled more cleanly if conversion functions returned Results,
    // but that would be a large and disruptive change to the overall code flow.
    final var postlude = TokenTree.of(
      """

              _ => panic!("Unknown enum variant: {}", value),
          })
      }
      """
    );

    return TokenTree.of(prelude, branches, postlude);
  }

  protected TokenTree enumFromDafnyFunction(final Shape enumShape) {
    String enumName = enumShape.getId().getName();
    String rustEnumName = toPascalCase(enumName);
    String sdkId = service
      .expectTrait(ServiceTrait.class)
      .getSdkId()
      .toLowerCase();
    String dafnyTypesModuleName = getDafnyTypesModuleName();
    Map<String, String> variables = Map.of(
      "sdkCrate",
      "aws_sdk_" + sdkId,
      "enumName",
      enumName,
      "rustEnumName",
      rustEnumName,
      "dafnyTypesModuleName",
      dafnyTypesModuleName
    );

    String sdkTypeName = evalTemplate(
      "$sdkCrate:L::types::$rustEnumName:L",
      variables
    );

    var prelude = TokenTree.of(
      evalTemplate(
        """
        #[allow(dead_code)]
        pub fn from_dafny(
            dafny_value: &crate::r#$dafnyTypesModuleName:L::$enumName:L,
        ) -> $sdkCrate:L::types::$rustEnumName:L {
            match dafny_value {

        """,
        variables
      )
    );

    var branches = TokenTree
      .of(
        enumShape
          .expectTrait(EnumTrait.class)
          .getValues()
          .stream()
          .map(e ->
            TokenTree.of(
              "crate::r#" +
              dafnyTypesModuleName +
              "::" +
              enumName +
              "::" +
              dafnyEnumName(e) +
              " {} => " +
              sdkTypeName +
              "::" +
              rustEnumName(e) +
              ","
            )
          )
      )
      .lineSeparated();
    final var postlude = TokenTree.of(
      """

          }
      }
      """
    );

    return TokenTree.of(prelude, branches, postlude);
  }

  protected Set<RustFile> allOperationConversionModules() {
    return serviceOperationShapes()
      .map(this::operationConversionModules)
      .flatMap(Collection::stream)
      .collect(Collectors.toSet());
  }

  protected abstract Set<RustFile> operationConversionModules(final OperationShape operationShape);

  private String rustEnumName(EnumDefinition ed) {
    return toPascalCase(ed.getValue());
  }

  private String dafnyEnumName(EnumDefinition ed) {
    return ed.getValue();
  }

  protected String getDafnyModuleName() {
    return service.getId().getNamespace().replace(".", "::");
  }

  protected String getDafnyInternalModuleName() {
    return "%s::internaldafny".formatted(getDafnyModuleName());
  }

  protected String getDafnyTypesModuleName() {
    return "%s::types".formatted(getDafnyInternalModuleName());
  }

  /**
   * Generates values for variables commonly used in service-specific templates.
   */
  protected HashMap<String, String> serviceVariables() {
    final HashMap<String, String> variables = new HashMap<>();
    variables.put("serviceName", service.getId().getName(service));
    return variables;
  }

  /**
   * Generates values for variables commonly used in operation-specific templates.
   */
  protected HashMap<String, String> operationVariables(final OperationShape operationShape) {
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
  protected HashMap<String, String> memberVariables(final MemberShape memberShape) {
    final HashMap<String, String> variables = new HashMap<>();
    variables.put("fieldName", toSnakeCase(memberShape.getMemberName()));
    variables.put("fieldType", rustTypeForShape(model.expectShape(memberShape.getTarget())));
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

  protected String operationErrorTypeName(final OperationShape operationShape) {
    return "%sError".formatted(operationName(operationShape));
  }

  // Currently only handles simple types, and doesn't account for any traits
  protected String rustTypeForShape(final Shape shape) {
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
