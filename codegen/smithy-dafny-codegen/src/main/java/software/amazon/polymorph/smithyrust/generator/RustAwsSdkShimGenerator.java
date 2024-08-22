package software.amazon.polymorph.smithyrust.generator;

import static software.amazon.polymorph.utils.IOUtils.evalTemplate;
import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toPascalCase;
import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toSnakeCase;

import java.nio.file.Path;
import java.util.HashMap;
import java.util.HashSet;
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
        .map(enumShape -> enumConversionModule(enumShape))
        .collect(Collectors.toSet())
    );

    result.add(conversionsModule());
    result.addAll(allOperationConversionModules());
    result.addAll(allStructureConversionModules());
    result.add(conversionsErrorModule());

    return result;
  }

  private RustFile clientModule() {
    String sdkId = service.expectTrait(ServiceTrait.class).getSdkId();
    String clientName = "%sClient".formatted(sdkId);
    String dafnyModuleName = getDafnyModuleName();
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
    String dafnyTypesModuleName = getDafnyTypesModuleName();
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
    String rustStructureName = toPascalCase(structureName);
    String template =
      """
      // Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.

      #[allow(dead_code)]
      pub fn to_dafny(
          value: &aws_sdk_$sdkId:L::types::$rustStructureName:L,
      ) -> ::std::rc::Rc<crate::r#$dafnyTypesModuleName:L::$structureName:L>{
        ::std::rc::Rc::new(
          crate::r#$dafnyTypesModuleName:L::$structureName:L::$structureName:L {
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
        getDafnyTypesModuleName(),
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
    String dafnyTypesModuleName = getDafnyTypesModuleName();
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
    variables.put("structureName", operationInputName(operationShape));
    variables.put(
      "variants",
      toDafnyVariantsForStructure(inputShape).toString()
    );

    return TokenTree.of(
      evalTemplate(
        """
        #[allow(dead_code)]
        pub fn to_dafny(
            value: &$sdkCrate:L::operation::$snakeCaseOperationName:L::$operationInputName:L,
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
    variables.put("structureName", operationInputName(operationShape));
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
        "_" + toSnakeCase(operationInputName(operationShape)),
        "_" + toSnakeCase(operationOutputName(operationShape))
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
    String operationName = operationShape.getId().getName();
    String snakeCaseOperationName = toSnakeCase(operationName);
    String sdkId = service
      .expectTrait(ServiceTrait.class)
      .getSdkId()
      .toLowerCase();
    String dafnyTypesModuleName = getDafnyTypesModuleName();

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

  protected TokenTree errorVariantToDafny(
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
          crate::r#$dafnyTypesModuleName:L::Error::$structureName:L {
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
        getDafnyTypesModuleName(),
        "variants",
        toDafnyVariantsForStructure(errorStructure).toString()
      )
    );
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
    String sdkId = service
      .expectTrait(ServiceTrait.class)
      .getSdkId()
      .toLowerCase();
    return "software::amazon::cryptography::services::%s".formatted(sdkId);
  }

  private String getSdkId() {
    return service.expectTrait(ServiceTrait.class).getSdkId();
  }

  private String getSdkCrate() {
    return "aws_sdk_%s".formatted(getSdkId());
  }

  @Override
  protected HashMap<String, String> serviceVariables() {
    final HashMap<String, String> variables = super.serviceVariables();
    variables.put("sdkId", getSdkId());
    variables.put("sdkCrate", getSdkCrate());
    return variables;
  }
}
