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
import software.amazon.polymorph.utils.MapUtils;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.model.Model;
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
      model
        .getStringShapesWithTrait(EnumTrait.class)
        .stream()
        .map(this::enumConversionModule)
        .collect(Collectors.toSet())
    );

    result.add(conversionsModule());
    result.addAll(allOperationConversionModules());
    result.addAll(allStructureConversionModules());
    result.add(conversionsErrorModule());
    // TODO union conversion modules

    return result;
  }

  private RustFile clientModule() {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      dafnyModuleVariables()
    );
    variables.put("clientName", "%sClient".formatted(getSdkId()));

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
      dafnyModuleVariables(),
      operationVariables(operationShape)
    );
    variables.put("clientName", "%sClient".formatted(getSdkId()));

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
    String template =
      """
      #[allow(dead_code)]
      pub fn to_dafny(
          value: &$sdkCrate:L::types::$rustStructureName:L,
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
      dafnyModuleVariables()
    );
    variables.put("structureName", structureName);
    variables.put("rustStructureName", toPascalCase(structureName));
    variables.put(
      "variants",
      toDafnyVariantsForStructure(structureShape).toString()
    );

    return TokenTree.of(evalTemplate(template, variables));
  }

  private TokenTree structureFromDafnyFunction(
    final StructureShape structureShape
  ) {
    String structureName = structureShape.getId().getName();
    // The builders smithy-rs generates only validate that required fields are provided,
    // and only produce `Result<...>` values if there are any required fields
    // (...that aren't structures, for some reason)
    String unwrapIfNeeded = structureShape
        .members()
        .stream()
        .anyMatch(m ->
          m.isRequired() && !model.expectShape(m.getTarget()).isStructureShape()
        )
      ? ".unwrap()"
      : "";
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      dafnyModuleVariables()
    );
    variables.put("structureName", structureName);
    variables.put("rustStructureName", toPascalCase(structureName));
    variables.put("snakeCaseStructureName", toSnakeCase(structureName));
    variables.put(
      "fluentMemberSetters",
      fluentMemberSettersForStructure(structureShape).toString()
    );
    variables.put("unwrapIfNeeded", unwrapIfNeeded);

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

  @Override
  protected TokenTree operationRequestToDafnyFunction(
    final OperationShape operationShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      dafnyModuleVariables(),
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
  protected TokenTree operationRequestFromDafnyFunction(
    final OperationShape operationShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      dafnyModuleVariables(),
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
      dafnyModuleVariables(),
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
      dafnyModuleVariables(),
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
      dafnyModuleVariables(),
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

  private RustFile errorConversionModule(final Shape errorStructure) {
    String structureName = errorStructure.getId().getName();
    String snakeCaseName = toSnakeCase(structureName);
    String pascalCaseName = toPascalCase(structureName);
    Path path = Path.of("src", "conversions", "error", snakeCaseName + ".rs");
    String template =
      """
      #[allow(dead_code)]
      pub fn to_dafny(
          value: $sdkCrate:L::types::error::$pascalCaseName:L,
      ) -> ::std::rc::Rc<crate::r#$dafnyTypesModuleName:L::Error>{
        ::std::rc::Rc::new(
          crate::r#$dafnyTypesModuleName:L::Error::$structureName:L {
            $variants:L
          }
        )
      }
      """;
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      dafnyModuleVariables()
    );
    variables.put("structureName", structureName);
    variables.put("pascalCaseName", pascalCaseName);
    variables.put(
      "variants",
      toDafnyVariantsForStructure(errorStructure).toString()
    );
    String evaluated = evalTemplate(template, variables);
    return new RustFile(path, TokenTree.of(evaluated));
  }

  private RustFile enumConversionModule(final Shape enumShape) {
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

  @Override
  protected String getDafnyModuleName() {
    return "software::amazon::cryptography::services::%s".formatted(
        getSdkId().toLowerCase()
      );
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
    variables.put("sdkId", getSdkId());
    variables.put("sdkCrate", getSdkCrate());
    return variables;
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
}
