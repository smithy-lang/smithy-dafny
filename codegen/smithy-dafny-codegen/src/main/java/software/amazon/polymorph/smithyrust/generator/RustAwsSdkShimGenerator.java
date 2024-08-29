package software.amazon.polymorph.smithyrust.generator;

import static software.amazon.polymorph.utils.IOUtils.evalTemplate;
import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toPascalCase;
import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toSnakeCase;

import java.nio.file.Path;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.utils.MapUtils;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.model.Model;
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
 * Generates all Rust modules needed to wrap
 * a Rust AWS SDK into a Dafny SDK.
 */
// TODO: There is a lot of duplication in the various calls to evalTemplate.
// The best way to clean this up is to thread SimpleCodeWriters through the methods and use the stateful
// putContext method, instead of trying to work purely functionality with map literals.
public class RustAwsSdkShimGenerator extends AbstractRustShimGenerator {

  public RustAwsSdkShimGenerator(Model model, ServiceShape service) {
    super(model, service);
  }

  @Override
  protected Set<RustFile> rustFiles() {
    Set<RustFile> result = new HashSet<>();
    result.add(clientModule());
    result.addAll(
      allErrorShapes()
        .map(this::errorConversionModule)
        .collect(Collectors.toSet())
    );

    result.addAll(
      ModelUtils
        .streamEnumShapes(model, service.getId().getNamespace())
        .map(this::enumConversionModule)
        .toList()
    );

    result.add(conversionsModule());
    result.addAll(allOperationConversionModules());
    result.addAll(allStructureConversionModules());
    result.add(conversionsErrorModule());
    // TODO union conversion modules

    return result;
  }

  private RustFile clientModule() {
    final Map<String, String> variables = serviceVariables();
    var preamble = TokenTree.of(
      evalTemplate(
        """
        use crate::conversions;

        struct Client {
            inner: $sdkCrate:L::Client,

            rt: tokio::runtime::Runtime,
        }

        impl dafny_runtime::UpcastObject<dyn std::any::Any> for Client {
            ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
        }

        impl dafny_runtime::UpcastObject<dyn crate::r#$dafnyTypesModuleName:L::I$clientName:L> for Client {
          ::dafny_runtime::UpcastObjectFn!(dyn crate::r#$dafnyTypesModuleName:L::I$clientName:L);
        }

        impl crate::r#$dafnyTypesModuleName:L::I$clientName:L
          for Client {

        """,
        variables
      )
    );

    var operations = TokenTree
      .of(
        service
          .getOperations()
          .stream()
          .map(id ->
            operationClientFunction(model.expectShape(id, OperationShape.class))
          )
      )
      .lineSeparated();

    var postamble = TokenTree.of(
      evalTemplate(
        """
        }

        #[allow(non_snake_case)]
        impl crate::r#$dafnyInternalModuleName:L::_default {
          pub fn $clientName:L() -> ::std::rc::Rc<
            crate::r#_Wrappers_Compile::Result<
              ::dafny_runtime::Object<dyn crate::r#$dafnyTypesModuleName:L::I$clientName:L>,
              ::std::rc::Rc<crate::r#$dafnyTypesModuleName:L::Error>
              >
            > {
            let rt_result = tokio::runtime::Builder::new_current_thread()
              .enable_all()
              .build();
            if rt_result.is_err() {
              return conversions::error::to_opaque_error_result(rt_result.err());
            }
            let rt = rt_result.unwrap();

            let shared_config = rt.block_on(aws_config::load_defaults(aws_config::BehaviorVersion::v2024_03_28()));
            let inner = $sdkCrate:L::Client::new(&shared_config);
            let client = Client { inner, rt };
            let dafny_client = ::dafny_runtime::upcast_object()(::dafny_runtime::object::new(client));
            std::rc::Rc::new(crate::r#_Wrappers_Compile::Result::Success { value: dafny_client })
          }
        }
        """,
        variables
      )
    );

    return new RustFile(
      Path.of("src", "client.rs"),
      TokenTree.of(preamble, operations, postamble)
    );
  }

  private TokenTree operationClientFunction(
    final OperationShape operationShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(operationShape)
    );

    final ShapeId outputShapeId = operationShape.getOutputShape();
    final String outputType = outputShapeId.equals(
        ShapeId.from("smithy.api#Unit")
      )
      ? "()"
      : evalTemplate(
        "std::rc::Rc<crate::r#$dafnyTypesModuleName:L::$operationOutputName:L>",
        variables
      );
    variables.put("outputType", outputType);

    return TokenTree.of(
      evalTemplate(
        """
        fn $operationName:L(&mut self, input: &std::rc::Rc<crate::r#$dafnyTypesModuleName:L::$operationInputName:L>)
          -> std::rc::Rc<crate::r#_Wrappers_Compile::Result<
            $outputType:L,
            std::rc::Rc<crate::r#$dafnyTypesModuleName:L::Error>
          >
        > {
          let native_result =\s
            self.rt.block_on(conversions::$snakeCaseOperationName:L::_$snakeCaseOperationName:L_request::from_dafny(input.clone(), self.inner.clone()).send());
          crate::standard_library_conversions::result_to_dafny(&native_result,\s
            conversions::$snakeCaseOperationName:L::_$snakeCaseOperationName:L_response::to_dafny,
            conversions::$snakeCaseOperationName:L::to_dafny_error)
        }
        """,
        variables
      )
    );
  }

  protected Set<RustFile> allStructureConversionModules() {
    return model
      .getStructureShapes()
      .stream()
      .filter(this::shouldGenerateStructForStructure)
      .map(this::structureConversionModule)
      .collect(Collectors.toSet());
  }

  @Override
  protected TokenTree operationRequestToDafnyFunction(
    final OperationShape operationShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(operationShape)
    );
    StructureShape inputShape = model.expectShape(
      operationShape.getInputShape(),
      StructureShape.class
    );
    variables.put(
      "variants",
      toDafnyVariantsForStructure(inputShape).toString()
    );

    return TokenTree.of(
      evalTemplate(
        """
        #[allow(dead_code)]
        pub fn to_dafny(
            value: &$sdkCrate:L::operation::$snakeCaseOperationName:L::$sdkOperationInputStruct:L,
        ) -> ::std::rc::Rc<
            crate::r#$dafnyTypesModuleName:L::$operationInputName:L,
        >{
            ::std::rc::Rc::new(crate::r#$dafnyTypesModuleName:L::$operationInputName:L::$operationInputName:L {
                $variants:L
            })
        }
        """,
        variables
      )
    );
  }

  @Override
  protected boolean isRustFieldRequired(
    final StructureShape parent,
    final MemberShape member
  ) {
    // These rules were mostly reverse-engineered from inspection of Rust SDKs,
    // and may not be complete!
    final Shape targetShape = model.expectShape(member.getTarget());
    return (
      super.isRustFieldRequired(parent, member) ||
      (operationIndex.isOutputStructure(parent) && targetShape.isIntegerShape())
    );
  }

  @Override
  protected boolean isStructureBuilderFallible(
    final StructureShape structureShape
  ) {
    // The builders smithy-rs generates only validate that required fields are provided,
    // and only produce `Result<...>` values if there are any required fields
    // (...that aren't structures, for some reason)
    return structureShape
      .members()
      .stream()
      .anyMatch(m ->
        m.isRequired() && !model.expectShape(m.getTarget()).isStructureShape()
      );
  }

  @Override
  protected TokenTree operationRequestFromDafnyFunction(
    final OperationShape operationShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(operationShape)
    );
    StructureShape inputShape = model.expectShape(
      operationShape.getInputShape(),
      StructureShape.class
    );
    variables.put(
      "fluentMemberSetters",
      fluentMemberSettersForStructure(inputShape).toString()
    );

    return TokenTree.of(
      evalTemplate(
        """
        #[allow(dead_code)]
        pub fn from_dafny(
            dafny_value: ::std::rc::Rc<
                crate::r#$dafnyTypesModuleName:L::$operationInputName:L,
            >,
            client: $sdkCrate:L::Client,
        ) -> $sdkCrate:L::operation::$snakeCaseOperationName:L::builders::$operationName:LFluentBuilder {
            client.$snakeCaseOperationName:L()
                  $fluentMemberSetters:L
        }
        """,
        variables
      )
    );
  }

  @Override
  protected TokenTree operationResponseToDafnyFunction(
    final OperationShape operationShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(operationShape)
    );
    StructureShape outputShape = model.expectShape(
      operationShape.getOutputShape(),
      StructureShape.class
    );
    variables.put("structureName", operationOutputName(operationShape));
    variables.put(
      "variants",
      toDafnyVariantsForStructure(outputShape).toString()
    );

    // Dafny maps smithy.api#Unit to ()
    if (outputShape.getId() == ShapeId.from("smithy.api#Unit")) {
      return TokenTree.of(
        evalTemplate(
          """
          #[allow(dead_code)]
          pub fn to_dafny(
              _value: &$sdkCrate:L::operation::$snakeCaseOperationName:L::$sdkOperationOutputStruct:L
          ) -> () {
              ()
          }
          """,
          variables
        )
      );
    } else {
      return TokenTree.of(
        evalTemplate(
          """
          #[allow(dead_code)]
          pub fn to_dafny(
              value: &$sdkCrate:L::operation::$snakeCaseOperationName:L::$sdkOperationOutputStruct:L
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
  }

  @Override
  protected TokenTree operationResponseFromDafnyFunction(
    final OperationShape operationShape
  ) {
    // No need for Dafny-to-Rust conversion
    return TokenTree.empty();
  }

  @Override
  protected Set<RustFile> operationConversionModules(
    final OperationShape operationShape
  ) {
    var operationModuleName = toSnakeCase(operationName(operationShape));
    var operationModuleContent = declarePubModules(
      Stream.of(
        "_" + toSnakeCase(operationName(operationShape) + "Request"),
        "_" + toSnakeCase(operationName(operationShape) + "Response")
      )
    );

    var errorToDafnyFunction = operationErrorToDafnyFunction(operationShape);

    RustFile outerModule = new RustFile(
      Path.of("src", "conversions", operationModuleName + ".rs"),
      TokenTree.of(operationModuleContent, errorToDafnyFunction)
    );

    RustFile requestModule = operationRequestConversionModule(operationShape);
    RustFile responseModule = operationResponseConversionModule(operationShape);

    return Set.of(outerModule, requestModule, responseModule);
  }

  protected TokenTree operationErrorToDafnyFunction(
    final OperationShape operationShape
  ) {
    TokenTree errorCases = TokenTree
      .of(
        operationShape
          .getErrors()
          .stream()
          .map(id ->
            errorVariantToDafny(
              operationShape,
              model.expectShape(id, StructureShape.class)
            )
          )
      )
      .lineSeparated();

    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(operationShape)
    );
    variables.put("errorCases", errorCases.toString());

    return TokenTree.of(
      evalTemplate(
        """
        #[allow(dead_code)]
        pub fn to_dafny_error(
            value: &::aws_smithy_runtime_api::client::result::SdkError<
                $sdkCrate:L::operation::$snakeCaseOperationName:L::$operationName:LError,
                ::aws_smithy_runtime_api::client::orchestrator::HttpResponse,
            >,
        ) -> ::std::rc::Rc<crate::r#$dafnyTypesModuleName:L::Error> {
            match value {
              $sdkCrate:L::error::SdkError::ServiceError(service_error) => match service_error.err() {
                $errorCases:L
                e => crate::conversions::error::to_opaque_error(e.to_string()),
              },
              _ => {
                crate::conversions::error::to_opaque_error(value.to_string())
              }
           }
        }

        """,
        variables
      )
    );
  }

  protected TokenTree errorVariantToDafny(
    final OperationShape operationShape,
    final StructureShape errorShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(operationShape)
    );
    String errorName = toPascalCase(errorShape.getId().getName());
    variables.put("errorName", errorName);
    variables.put("snakeCaseErrorName", toSnakeCase(errorName));

    return TokenTree.of(
      evalTemplate(
        """
                $sdkCrate:L::operation::$snakeCaseOperationName:L::$operationName:LError::$errorName:L(e) =>
                    crate::conversions::error::$snakeCaseErrorName:L::to_dafny(e.clone()),
        """,
        variables
      )
    );
  }

  private RustFile errorConversionModule(final StructureShape errorStructure) {
    String structureName = errorStructure.getId().getName();
    String snakeCaseName = toSnakeCase(structureName);
    String pascalCaseName = toPascalCase(structureName);
    Path path = Path.of("src", "conversions", "error", snakeCaseName + ".rs");
    String template =
      """
      #[allow(dead_code)]
      pub fn to_dafny(
          value: $rustTypesModuleName:L::error::$pascalCaseName:L,
      ) -> ::std::rc::Rc<crate::r#$dafnyTypesModuleName:L::Error>{
        ::std::rc::Rc::new(
          crate::r#$dafnyTypesModuleName:L::Error::$structureName:L {
            $variants:L
          }
        )
      }
      """;
    final Map<String, String> variables = serviceVariables();
    variables.put("structureName", structureName);
    variables.put("pascalCaseName", pascalCaseName);
    variables.put(
      "variants",
      toDafnyVariantsForStructure(errorStructure).toString()
    );
    return new RustFile(path, TokenTree.of(evalTemplate(template, variables)));
  }

  @Override
  protected String getDafnyModuleName() {
    return "software::amazon::cryptography::services::%s".formatted(
        getSdkId().toLowerCase()
      );
  }

  @Override
  protected String getRustTypesModuleName() {
    return "%s::types".formatted(getSdkCrate());
  }

  private String getSdkId() {
    return service.expectTrait(ServiceTrait.class).getSdkId();
  }

  private String getSdkCrate() {
    return "aws_sdk_%s".formatted(getSdkId().toLowerCase(Locale.ROOT));
  }

  @Override
  protected HashMap<String, String> serviceVariables() {
    final HashMap<String, String> variables = super.serviceVariables();
    final String sdkId = getSdkId();
    variables.put("sdkId", sdkId);
    variables.put("sdkCrate", getSdkCrate());
    variables.put("clientName", "%sClient".formatted(sdkId));
    return variables;
  }

  @Override
  protected String syntheticOperationInputName(OperationShape operationShape) {
    return operationName(operationShape) + "Request";
  }

  @Override
  protected String syntheticOperationOutputName(OperationShape operationShape) {
    return operationName(operationShape) + "Response";
  }

  private String sdkOperationInputStruct(final OperationShape operationShape) {
    return operationName(operationShape) + "Input";
  }

  private String sdkOperationOutputStruct(final OperationShape operationShape) {
    return operationName(operationShape) + "Output";
  }

  @Override
  protected HashMap<String, String> operationVariables(
    OperationShape operationShape
  ) {
    final HashMap<String, String> variables = super.operationVariables(
      operationShape
    );
    variables.put(
      "sdkOperationInputStruct",
      sdkOperationInputStruct(operationShape)
    );
    variables.put(
      "sdkOperationOutputStruct",
      sdkOperationOutputStruct(operationShape)
    );
    return variables;
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
              crate::conversions::%s::to_dafny(%s)
              """.formatted(structureShapeName, rustValue)
            );
          }
        } else {
          yield TokenTree.of(
            """
            ::std::rc::Rc::new(match &%s {
                Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::conversions::%s::to_dafny(x) },
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
}
