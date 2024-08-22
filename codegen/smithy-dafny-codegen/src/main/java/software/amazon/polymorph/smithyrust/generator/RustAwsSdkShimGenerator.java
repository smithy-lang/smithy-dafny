package software.amazon.polymorph.smithyrust.generator;

import static software.amazon.polymorph.utils.IOUtils.evalTemplate;
import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toPascalCase;
import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toSnakeCase;

import java.nio.file.Path;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import software.amazon.polymorph.utils.IOUtils;
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

/**
 * Generates all Rust modules needed to wrap
 * a Rust AWS SDK into a Dafny SDK.
 */
// TODO: There is a lot of duplication in the various calls to evalTemplate.
// The best way to clean this up is to thread SimpleCodeWriters through the methods and use the stateful
// putContext method, instead of trying to work purely functionality with map literals.
public class RustAwsSdkShimGenerator {

  private final Model model;
  private final ServiceShape service;
  private final OperationIndex operationIndex;

  public RustAwsSdkShimGenerator(Model model, ServiceShape service) {
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

  private Set<RustFile> rustFiles() {
    ServiceShape service = model.getServiceShapes().stream().findFirst().get();

    Set<RustFile> result = new HashSet<>();
    result.add(clientModule());
    result.addAll(
      allErrorShapes()
        .map(errorShape -> errorConversionModule(service, errorShape))
        .collect(Collectors.toSet())
    );

    result.addAll(
      model
        .getStringShapesWithTrait(EnumTrait.class)
        .stream()
        .map(enumShape -> enumConversionModule(service, enumShape))
        .collect(Collectors.toSet())
    );

    result.add(conversionsModuleFile(model, service));
    result.addAll(allOperationConversionModules());
    result.addAll(allStructureConversionModules());
    result.add(conversionsErrorModule(model, service));

    return result;
  }

  private RustFile clientModule() {
    String sdkId = service.expectTrait(ServiceTrait.class).getSdkId();
    String clientName = "%sClient".formatted(sdkId);
    String dafnyModuleName =
      "software::amazon::cryptography::services::%s::internaldafny".formatted(
          sdkId.toLowerCase()
        );
    String dafnyTypesModuleName = "%s::types".formatted(dafnyModuleName);
    Map<String, String> variables = Map.of(
      "sdkId",
      sdkId.toLowerCase(),
      "clientName",
      clientName,
      "dafnyModuleName",
      dafnyModuleName,
      "dafnyTypesModuleName",
      dafnyTypesModuleName
    );

    var preamble = TokenTree.of(
      evalTemplate(
        """
        use crate::conversions;

        struct Client {
            inner: aws_sdk_$sdkId:L::Client,

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
        impl crate::r#$dafnyModuleName:L::_default {
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
            let inner = aws_sdk_$sdkId:L::Client::new(&shared_config);
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
    String operationName = operationShape.getId().getName();
    String snakeCaseOperationName = toSnakeCase(operationName);
    String inputShapeName = operationShape.getInputShape().getName();
    ShapeId outputShapeId = operationShape.getOutputShape();
    String outputShapeName = outputShapeId.getName();
    String sdkId = service.expectTrait(ServiceTrait.class).getSdkId();
    String clientName = "%sClient".formatted(sdkId);
    String dafnyModuleName =
      "software::amazon::cryptography::services::%s::internaldafny".formatted(
          sdkId.toLowerCase()
        );
    String dafnyTypesModuleName = "%s::types".formatted(dafnyModuleName);
    String outputType = outputShapeId.equals(ShapeId.from("smithy.api#Unit"))
      ? "()"
      : evalTemplate(
        "std::rc::Rc<crate::r#$dafnyTypesModuleName:L::$outputShapeName:L>",
        Map.of(
          "outputShapeName",
          outputShapeName,
          "dafnyTypesModuleName",
          dafnyTypesModuleName
        )
      );
    Map<String, String> variables = Map.of(
      "operationName",
      operationName,
      "snakeCaseOperationName",
      snakeCaseOperationName,
      "inputShapeName",
      inputShapeName,
      "outputType",
      outputType,
      "sdkId",
      sdkId.toLowerCase(),
      "clientName",
      clientName,
      "dafnyModuleName",
      dafnyModuleName,
      "dafnyTypesModuleName",
      dafnyTypesModuleName
    );

    return TokenTree.of(
      evalTemplate(
        """
        fn $operationName:L(&mut self, input: &std::rc::Rc<crate::r#$dafnyTypesModuleName:L::$inputShapeName:L>)
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

  private Stream<StructureShape> allErrorShapes() {
    return model
      .getOperationShapes()
      .stream()
      .flatMap(operationShape -> operationShape.getErrors().stream())
      .distinct()
      .map(errorShapeId -> model.expectShape(errorShapeId, StructureShape.class)
      );
  }

  private Set<RustFile> allOperationConversionModules() {
    return service
      .getOperations()
      .stream()
      .map(shapeId ->
        operationConversionModules(
          model.expectShape(shapeId, OperationShape.class)
        )
      )
      .flatMap(s -> s.stream())
      .collect(Collectors.toSet());
  }

  private Set<RustFile> operationConversionModules(
    final OperationShape operationShape
  ) {
    var operationModuleName = toSnakeCase(operationShape.getId().getName());
    var operationModuleContent = declarePubModules(
      Stream.of(
        "_" + operationModuleName + "_request",
        "_" + operationModuleName + "_response"
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

  private TokenTree operationErrorToDafnyFunction(
    final OperationShape operationShape
  ) {
    String operationName = operationShape.getId().getName();
    String snakeCaseOperationName = toSnakeCase(operationName);
    String sdkId = service
      .expectTrait(ServiceTrait.class)
      .getSdkId()
      .toLowerCase();
    String dafnyTypesModuleName =
      "software::amazon::cryptography::services::%s::internaldafny::types".formatted(
          sdkId
        );

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

    Map<String, String> variables = Map.of(
      "sdkCrate",
      "aws_sdk_" + sdkId,
      "operationName",
      operationName,
      "snakeCaseOperationName",
      snakeCaseOperationName,
      "dafnyTypesModuleName",
      dafnyTypesModuleName,
      "errorCases",
      errorCases.toString()
    );

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

  private TokenTree errorVariantToDafny(
    final OperationShape operationShape,
    final StructureShape errorShape
  ) {
    String operationName = operationShape.getId().getName();
    String errorName = toPascalCase(errorShape.getId().getName());
    String sdkId = service
      .expectTrait(ServiceTrait.class)
      .getSdkId()
      .toLowerCase();
    Map<String, String> variables = Map.of(
      "sdkId",
      sdkId,
      "operationName",
      operationName,
      "snakeCaseOperationName",
      toSnakeCase(operationName),
      "errorName",
      errorName,
      "snakeCaseErrorName",
      toSnakeCase(errorName)
    );

    return TokenTree.of(
      evalTemplate(
        """
                aws_sdk_$sdkId:L::operation::$snakeCaseOperationName:L::$operationName:LError::$errorName:L(e) =>
                    crate::conversions::error::$snakeCaseErrorName:L::to_dafny(e.clone()),
        """,
        variables
      )
    );
  }

  private RustFile operationRequestConversionModule(
    final OperationShape operationShape
  ) {
    var operationModuleName = toSnakeCase(operationShape.getId().getName());

    var toDafnyFunction = operationRequestToDafnyFunction(operationShape);
    var fromDafnyFunction = operationRequestFromDafnyFunction(operationShape);

    return new RustFile(
      Path.of(
        "src",
        "conversions",
        operationModuleName,
        "_" + operationModuleName + "_request.rs"
      ),
      TokenTree.of(toDafnyFunction, fromDafnyFunction).lineSeparated()
    );
  }

  private TokenTree operationRequestToDafnyFunction(
    final OperationShape operationShape
  ) {
    StructureShape inputShape = model.expectShape(
      operationShape.getInputShape(),
      StructureShape.class
    );
    String operationName = operationShape.getId().getName();
    String snakeCaseOperationName = toSnakeCase(operationName);
    String sdkId = service
      .expectTrait(ServiceTrait.class)
      .getSdkId()
      .toLowerCase();
    String dafnyTypesModuleName =
      "software::amazon::cryptography::services::%s::internaldafny::types".formatted(
          sdkId
        );
    String structureName = inputShape.getId().getName();
    Map<String, String> variables = Map.of(
      "sdkCrate",
      "aws_sdk_" + sdkId,
      "operationName",
      operationName,
      "structureName",
      structureName,
      "snakeCaseOperationName",
      snakeCaseOperationName,
      "dafnyTypesModuleName",
      dafnyTypesModuleName,
      "variants",
      toDafnyVariantsForStructure(inputShape).toString()
    );

    return TokenTree.of(
      evalTemplate(
        """
        #[allow(dead_code)]
        pub fn to_dafny(
            value: &$sdkCrate:L::operation::$snakeCaseOperationName:L::$operationName:LInput
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

  private TokenTree operationRequestFromDafnyFunction(
    final OperationShape operationShape
  ) {
    StructureShape inputShape = model.expectShape(
      operationShape.getInputShape(),
      StructureShape.class
    );
    String operationName = operationShape.getId().getName();
    String snakeCaseOperationName = toSnakeCase(operationName);
    String sdkId = service
      .expectTrait(ServiceTrait.class)
      .getSdkId()
      .toLowerCase();
    String dafnyTypesModuleName =
      "software::amazon::cryptography::services::%s::internaldafny::types".formatted(
          sdkId
        );
    String structureName = inputShape.getId().getName();
    Map<String, String> variables = Map.of(
      "sdkCrate",
      "aws_sdk_" + sdkId,
      "operationName",
      operationName,
      "structureName",
      structureName,
      "snakeCaseOperationName",
      snakeCaseOperationName,
      "dafnyTypesModuleName",
      dafnyTypesModuleName,
      "fluentMemberSetters",
      fluentMemberSettersForStructure(inputShape).toString()
    );

    return TokenTree.of(
      evalTemplate(
        """
        #[allow(dead_code)]
        pub fn from_dafny(
            dafny_value: ::std::rc::Rc<
                crate::r#$dafnyTypesModuleName:L::$structureName:L,
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

  private TokenTree fluentMemberSettersForStructure(Shape shape) {
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

  private RustFile operationResponseConversionModule(
    final OperationShape operationShape
  ) {
    var operationModuleName = toSnakeCase(operationShape.getId().getName());

    var toDafnyFunction = operationResponseToDafnyFunction(operationShape);

    return new RustFile(
      Path.of(
        "src",
        "conversions",
        operationModuleName,
        "_" + operationModuleName + "_response.rs"
      ),
      toDafnyFunction
    );
  }

  private TokenTree operationResponseToDafnyFunction(
    final OperationShape operationShape
  ) {
    StructureShape outputShape = model.expectShape(
      operationShape.getOutputShape(),
      StructureShape.class
    );
    String operationName = operationShape.getId().getName();
    String snakeCaseOperationName = toSnakeCase(operationName);
    String sdkId = service
      .expectTrait(ServiceTrait.class)
      .getSdkId()
      .toLowerCase();
    String dafnyTypesModuleName =
      "software::amazon::cryptography::services::%s::internaldafny::types".formatted(
          sdkId
        );
    String structureName = outputShape.getId().getName();
    Map<String, String> variables = Map.of(
      "sdkCrate",
      "aws_sdk_" + sdkId,
      "operationName",
      operationName,
      "structureName",
      structureName,
      "snakeCaseOperationName",
      snakeCaseOperationName,
      "dafnyTypesModuleName",
      dafnyTypesModuleName,
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
              _value: &$sdkCrate:L::operation::$snakeCaseOperationName:L::$operationName:LOutput
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
              value: &$sdkCrate:L::operation::$snakeCaseOperationName:L::$operationName:LOutput
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

  private TokenTree toDafnyVariantsForStructure(Shape shape) {
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

  private RustFile conversionsErrorModule(
    final Model model,
    final ServiceShape service
  ) {
    TokenTree modulesDeclarations = declarePubModules(
      allErrorShapes()
        .map(structureShape -> toSnakeCase(structureShape.getId().getName()))
    );

    String sdkId = service
      .expectTrait(ServiceTrait.class)
      .getSdkId()
      .toLowerCase();
    String dafnyTypesModuleName =
      "software::amazon::cryptography::services::%s::internaldafny::types".formatted(
          sdkId
        );

    Map<String, String> variables = Map.of(
      "sdkCrate",
      "aws_sdk_" + sdkId,
      "dafnyTypesModuleName",
      dafnyTypesModuleName
    );
    TokenTree toDafnyOpaqueErrorFunctions = TokenTree.of(
      evalTemplate(
        """
        /// Wraps up an arbitrary Rust Error value as a Dafny Error
        pub fn to_opaque_error<E: 'static>(value: E) ->
          ::std::rc::Rc<crate::r#$dafnyTypesModuleName:L::Error>
        {
            let error_obj: ::dafny_runtime::Object<dyn::std::any::Any> = ::dafny_runtime::Object(Some(
                ::std::rc::Rc::new(::std::cell::UnsafeCell::new(value)),
            ));
            ::std::rc::Rc::new(
            crate::r#$dafnyTypesModuleName:L::Error::Opaque {
                obj: error_obj,
            },
          )
        }

        /// Wraps up an arbitrary Rust Error value as a Dafny Result<T, Error>.Failure
        pub fn to_opaque_error_result<T: dafny_runtime::DafnyType, E: 'static>(value: E) ->
          ::std::rc::Rc<
            crate::_Wrappers_Compile::Result<
              T,
              ::std::rc::Rc<crate::r#$dafnyTypesModuleName:L::Error>
            >
          >
        {
            ::std::rc::Rc::new(
                crate::_Wrappers_Compile::Result::Failure {
                    error: to_opaque_error(value),
                },
            )
        }

        """,
        variables
      )
    );
    return new RustFile(
      Path.of("src", "conversions", "error.rs"),
      TokenTree.of(modulesDeclarations, toDafnyOpaqueErrorFunctions)
    );
  }

  private RustFile conversionsModuleFile(
    final Model model,
    final ServiceShape service
  ) {
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

  private TokenTree declarePubModules(Stream<String> moduleNames) {
    return TokenTree
      .of(
        moduleNames
          .sorted()
          .map(module -> TokenTree.of("pub mod " + module + ";\n"))
      )
      .lineSeparated();
  }

  private RustFile errorConversionModule(
    final ServiceShape service,
    final Shape errorStructure
  ) {
    String structureName = errorStructure.getId().getName();
    String snakeCaseName = toSnakeCase(structureName);
    String pascalCaseName = toPascalCase(structureName);
    Path path = Path.of("src", "conversions", "error", snakeCaseName + ".rs");
    String template =
      """
      // Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.

      #[allow(dead_code)]
      pub fn to_dafny(
          value: aws_sdk_$sdkId:L::types::error::$pascalCaseName:L,
      ) -> ::std::rc::Rc<crate::r#$dafnyTypesModuleName:L::Error>{
        ::std::rc::Rc::new(
          crate::r#software::amazon::cryptography::services::$sdkId:L::internaldafny::types::Error::$structureName:L {
            $variants:L
          }
        )
      }
      """;
    String sdkId = service
      .expectTrait(ServiceTrait.class)
      .getSdkId()
      .toLowerCase();
    String evaluated = evalTemplate(
      template,
      Map.of(
        "sdkId",
        sdkId,
        "structureName",
        structureName,
        "pascalCaseName",
        pascalCaseName,
        "dafnyTypesModuleName",
        "software::amazon::cryptography::services::%s::internaldafny::types".formatted(
            sdkId
          ),
        "variants",
        toDafnyVariantsForStructure(errorStructure).toString()
      )
    );
    return new RustFile(path, TokenTree.of(evaluated));
  }

  private boolean shouldGenerateStructForStructure(
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

  private boolean shouldGenerateEnumForUnion(UnionShape unionShape) {
    return unionShape
      .getId()
      .getNamespace()
      .equals(service.getId().getNamespace());
  }

  private Set<RustFile> allStructureConversionModules() {
    return model
      .getStructureShapes()
      .stream()
      .filter(this::shouldGenerateStructForStructure)
      .map(this::structureConversionModule)
      .collect(Collectors.toSet());
  }

  private RustFile structureConversionModule(
    final StructureShape structureShape
  ) {
    String structureName = structureShape.getId().getName();
    String snakeCaseName = toSnakeCase(structureName);
    Path path = Path.of("src", "conversions", snakeCaseName + ".rs");
    return new RustFile(
      path,
      TokenTree.of(
        structureToDafnyFunction(structureShape),
        structureFromDafnyFunction(structureShape)
      )
    );
  }

  private TokenTree structureToDafnyFunction(
    final StructureShape structureShape
  ) {
    String structureName = structureShape.getId().getName();
    String rustStructureName = toPascalCase(structureName);
    String template =
      """
      // Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.

      #[allow(dead_code)]
      pub fn to_dafny(
          value: &aws_sdk_$sdkId:L::types::$rustStructureName:L,
      ) -> ::std::rc::Rc<crate::r#$dafnyTypesModuleName:L::$structureName:L>{
        ::std::rc::Rc::new(
          crate::r#software::amazon::cryptography::services::$sdkId:L::internaldafny::types::$structureName:L::$structureName:L {
              $variants:L
          }
        )
      }
      """;
    String sdkId = service
      .expectTrait(ServiceTrait.class)
      .getSdkId()
      .toLowerCase();
    String evaluated = evalTemplate(
      template,
      Map.of(
        "sdkId",
        sdkId,
        "structureName",
        structureName,
        "rustStructureName",
        rustStructureName,
        "dafnyTypesModuleName",
        "software::amazon::cryptography::services::%s::internaldafny::types".formatted(
            sdkId
          ),
        "variants",
        toDafnyVariantsForStructure(structureShape).toString()
      )
    );
    return TokenTree.of(evaluated);
  }

  private TokenTree structureFromDafnyFunction(
    final StructureShape structureShape
  ) {
    String structureName = structureShape.getId().getName();
    String rustStructureName = toPascalCase(structureName);
    String snakeCaseStructureName = toSnakeCase(structureName);
    String sdkId = service
      .expectTrait(ServiceTrait.class)
      .getSdkId()
      .toLowerCase();
    String dafnyTypesModuleName =
      "software::amazon::cryptography::services::%s::internaldafny::types".formatted(
          sdkId
        );
    // The builders smithy-rs generates only validate that required fields are provided,
    // and only produce `Result<...>` values if there are any required fields.
    String unwrapIfNeeded = structureShape
        .members()
        .stream()
        .anyMatch(m -> m.isRequired())
      ? ".unwrap()"
      : "";
    Map<String, String> variables = Map.of(
      "sdkCrate",
      "aws_sdk_" + sdkId,
      "structureName",
      structureName,
      "rustStructureName",
      rustStructureName,
      "snakeCaseStructureName",
      snakeCaseStructureName,
      "dafnyTypesModuleName",
      dafnyTypesModuleName,
      "fluentMemberSetters",
      fluentMemberSettersForStructure(structureShape).toString(),
      "unwrapIfNeeded",
      unwrapIfNeeded
    );

    return TokenTree.of(
      evalTemplate(
        """
        #[allow(dead_code)]
        pub fn from_dafny(
            dafny_value: ::std::rc::Rc<
                crate::r#$dafnyTypesModuleName:L::$structureName:L,
            >,
        ) -> $sdkCrate:L::types::$rustStructureName:L {
            $sdkCrate:L::types::$rustStructureName:L::builder()
                  $fluentMemberSetters:L
                  .build()
                  $unwrapIfNeeded:L
        }
        """,
        variables
      )
    );
  }

  private RustFile enumConversionModule(
    final ServiceShape service,
    final Shape enumShape
  ) {
    Path path = Path.of(
      "src",
      "conversions",
      toSnakeCase(enumShape.getId().getName()) + ".rs"
    );

    return new RustFile(
      path,
      TokenTree.of(
        enumToDafnyFunction(enumShape),
        enumFromDafnyFunction(enumShape)
      )
    );
  }

  private TokenTree enumToDafnyFunction(final Shape enumShape) {
    String enumName = enumShape.getId().getName();
    String rustEnumName = toPascalCase(enumName);
    String sdkId = service
      .expectTrait(ServiceTrait.class)
      .getSdkId()
      .toLowerCase();
    String dafnyTypesModuleName =
      "software::amazon::cryptography::services::%s::internaldafny::types".formatted(
          sdkId
        );
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

  private TokenTree enumFromDafnyFunction(final Shape enumShape) {
    String enumName = enumShape.getId().getName();
    String rustEnumName = toPascalCase(enumName);
    String sdkId = service
      .expectTrait(ServiceTrait.class)
      .getSdkId()
      .toLowerCase();
    String dafnyTypesModuleName =
      "software::amazon::cryptography::services::%s::internaldafny::types".formatted(
          sdkId
        );
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

  private String rustEnumName(EnumDefinition ed) {
    return toPascalCase(ed.getValue());
  }

  private String dafnyEnumName(EnumDefinition ed) {
    return ed.getValue();
  }
}
