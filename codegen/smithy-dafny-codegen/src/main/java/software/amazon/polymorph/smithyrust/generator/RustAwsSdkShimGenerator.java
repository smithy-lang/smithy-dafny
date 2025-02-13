package software.amazon.polymorph.smithyrust.generator;

import static software.amazon.polymorph.utils.IOUtils.evalTemplate;
import static software.amazon.polymorph.utils.IOUtils.evalTemplateResource;
import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toPascalCase;
import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toSnakeCase;

import com.google.common.collect.MoreCollectors;
import java.nio.file.Path;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import software.amazon.polymorph.CodegenEngine;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.utils.BoundOperationShape;
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
import software.amazon.smithy.model.traits.BoxTrait;
import software.amazon.smithy.model.traits.DefaultTrait;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.RequiredTrait;
import software.amazon.smithy.model.traits.UnitTypeTrait;

/**
 * Generates all Rust modules needed to wrap
 * a Rust AWS SDK into a Dafny SDK.
 */
public class RustAwsSdkShimGenerator extends AbstractRustShimGenerator {

  private final Set<CodegenEngine.GenerationAspect> generationAspects;

  public RustAwsSdkShimGenerator(
    MergedServicesGenerator mergedGenerator,
    Model model,
    ServiceShape service,
    Set<CodegenEngine.GenerationAspect> generationAspects
  ) {
    super(mergedGenerator, model, service);
    this.generationAspects = generationAspects;
  }

  @Override
  protected Set<RustFile> rustFiles() {
    Set<RustFile> result = new HashSet<>();
    result.add(clientModule());

    result.add(conversionsModule());
    result.add(typesModule());
    result.add(typesErrorModule());
    result.addAll(allOperationConversionModules());
    result.addAll(allStructureConversionModules());
    result.addAll(allEnumConversionModules());
    result.addAll(allErrorConversionModules());
    result.addAll(allUnionConversionModules());
    result.add(conversionsErrorModule());
    result.add(conversionsClientModule());

    return result;
  }

  private RustFile typesModule() {
    return new RustFile(
      rootPathForShape(service).resolve("types.rs"),
      TokenTree.of("pub mod error;")
    );
  }

  private RustFile clientModule() {
    final Map<String, String> variables = serviceVariables();
    variables.put(
      "operations",
      TokenTree
        .of(
          service
            .getOperations()
            .stream()
            .map(id ->
              operationClientFunction(
                service,
                model.expectShape(id, OperationShape.class)
              )
            )
        )
        .lineSeparated()
        .toString()
    );

    var preamble = TokenTree.of(
      evalTemplate(
        """
        use std::sync::LazyLock;
        use $rustRootModuleName:L::conversions;

        #[derive(::std::clone::Clone, ::std::fmt::Debug)]
        pub struct Client {
            pub inner: $sdkCrate:L::Client
        }

        impl ::std::cmp::PartialEq for Client {
          fn eq(&self, other: &Self) -> bool {
            false
          }
        }

        impl ::std::convert::Into<Client> for $sdkCrate:L::Client {
            fn into(self) -> Client {
                Client { inner: self }
            }
        }

        /// A runtime for executing operations on the asynchronous client in a blocking manner.
        /// Necessary because Dafny only generates synchronous code.
        static dafny_tokio_runtime: LazyLock<tokio::runtime::Runtime> = LazyLock::new(|| {
            tokio::runtime::Builder::new_multi_thread()
                  .enable_all()
                  .build()
                  .unwrap()
        });

        impl dafny_runtime::UpcastObject<::dafny_runtime::DynAny> for Client {
            ::dafny_runtime::UpcastObjectFn!(::dafny_runtime::DynAny);
        }

        impl dafny_runtime::UpcastObject<dyn crate::r#$dafnyTypesModuleName:L::I$clientName:L> for Client {
          ::dafny_runtime::UpcastObjectFn!(dyn crate::r#$dafnyTypesModuleName:L::I$clientName:L);
        }

        impl crate::r#$dafnyTypesModuleName:L::I$clientName:L
          for Client {
          $operations:L
        }
        """,
        variables
      )
    );

    final TokenTree postamble;
    if (
      generationAspects.contains(
        CodegenEngine.GenerationAspect.CLIENT_CONSTRUCTORS
      )
    ) {
      postamble =
        TokenTree.of(
          evalTemplate(
            """
            #[allow(non_snake_case)]
            impl crate::r#$dafnyInternalModuleName:L::_default {
              pub fn $clientName:L() -> ::dafny_runtime::Rc<
                crate::r#_Wrappers_Compile::Result<
                  ::dafny_runtime::Object<dyn crate::r#$dafnyTypesModuleName:L::I$clientName:L>,
                  ::dafny_runtime::Rc<crate::r#$dafnyTypesModuleName:L::Error>
                  >
                > {
                let shared_config = dafny_tokio_runtime.block_on(aws_config::load_defaults(aws_config::BehaviorVersion::v2024_03_28()));
                let inner = $sdkCrate:L::Client::new(&shared_config);
                let client = Client { inner };
                let dafny_client = ::dafny_runtime::upcast_object()(::dafny_runtime::object::new(client));
                dafny_runtime::Rc::new(crate::r#_Wrappers_Compile::Result::Success { value: dafny_client })
              }
            }
            """,
            variables
          )
        );
    } else {
      postamble = TokenTree.empty();
    }

    return new RustFile(
      rootPathForShape(service).resolve("client.rs"),
      TokenTree.of(preamble, postamble)
    );
  }

  private TokenTree operationClientFunction(
    final Shape bindingShape,
    final OperationShape operationShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(bindingShape, operationShape)
    );

    final StructureShape inputShape = operationIndex
      .getInputShape(operationShape)
      .get();
    final StructureShape outputShape = operationIndex
      .getOutputShape(operationShape)
      .get();
    final String outputType = outputShape.hasTrait(UnitTypeTrait.class)
      ? "()"
      : evalTemplate(
        "dafny_runtime::Rc<crate::r#$dafnyTypesModuleName:L::$operationOutputName:L>",
        variables
      );
    variables.put("outputType", outputType);

    variables.put(
      "fluentSetters",
      inputShape
        .members()
        .stream()
        .map(member ->
          evalTemplate(
            ".set_$fieldName:L(inner_input.r#$fieldName:L)",
            structureMemberVariables(member)
          )
        )
        .collect(Collectors.joining("\n"))
    );

    variables.put(
      "outputToDafnyMapper",
      outputShape.hasTrait(UnitTypeTrait.class)
        ? "|x| ()"
        : evalTemplate(
          "$rustRootModuleName:L::conversions::$snakeCaseOperationName:L::_$snakeCaseOperationName:L_response::to_dafny",
          variables
        )
    );

    return TokenTree.of(
      evalTemplate(
        """
        fn $operationName:L(&self, input: &dafny_runtime::Rc<crate::r#$dafnyTypesModuleName:L::$operationInputName:L>)
          -> dafny_runtime::Rc<crate::r#_Wrappers_Compile::Result<
            $outputType:L,
            dafny_runtime::Rc<crate::r#$dafnyTypesModuleName:L::Error>
          >
        > {
          let inner_input = $rustRootModuleName:L::conversions::$snakeCaseOperationName:L::_$snakeCaseOperationName:L_request::from_dafny(input.clone());
          let native_result = tokio::task::block_in_place(|| {
            dafny_tokio_runtime.block_on(async {
              self.inner.$snakeCaseOperationName:L()
                $fluentSetters:L
                .send()
                .await
              })
            });
          crate::standard_library_conversions::result_to_dafny(&native_result,\s
            $outputToDafnyMapper:L,
            $rustRootModuleName:L::conversions::$snakeCaseOperationName:L::to_dafny_error)
        }
        """,
        variables
      )
    );
  }

  protected RustFile conversionsClientModule() {
    TokenTree clientConversionFunctions = TokenTree.of(
      evalTemplateResource(
        getClass(),
        "runtimes/rust/conversions/client_awssdk.rs",
        serviceVariables()
      )
    );
    return new RustFile(
      rootPathForShape(service).resolve("conversions").resolve("client.rs"),
      clientConversionFunctions
    );
  }

  protected RustFile conversionsErrorModule() {
    final Map<String, String> variables = serviceVariables();

    TokenTree modulesDeclarations = RustUtils.declarePubModules(
      allErrorShapes()
        .map(structureShape -> toSnakeCase(structureShape.getId().getName()))
    );

    variables.put(
      "qualifiedRustServiceErrorType",
      topLevelNameForShape(service) + "::types::error::Error"
    );

    final String toDafnyArms = allErrorShapes()
      .map(errorShape ->
        evalTemplate(
          """
          $qualifiedRustServiceErrorType:L::$rustErrorName:L { error } =>
              $rustRootModuleName:L::conversions::error::$snakeCaseErrorName:L::to_dafny(error),
          """,
          MapUtils.merge(errorVariables(errorShape), variables)
        )
      )
      .collect(Collectors.joining("\n"));
    variables.put("toDafnyArms", toDafnyArms);

    final String fromDafnyArms = allErrorShapes()
      .map(errorShape ->
        evalTemplate(
          """
          crate::r#$dafnyTypesModuleName:L::Error::$errorName:L { $errorMessageMemberName:L, .. } =>
            $qualifiedRustServiceErrorType:L::$rustErrorName:L {
              error: $sdkCrate:L::types::error::$rustErrorName:L::builder()
                .set_message(crate::standard_library_conversions::ostring_from_dafny($errorMessageMemberName:L.clone()))
                .build()
            },
          """,
          MapUtils.merge(errorVariables(errorShape), variables)
        )
      )
      .collect(Collectors.joining("\n"));
    variables.put("fromDafnyArms", fromDafnyArms);

    final TokenTree sdkContent = TokenTree.of(
      evalTemplateResource(
        getClass(),
        "runtimes/rust/conversions/error_awssdk.rs",
        variables
      )
    );
    final TokenTree toDafnyOpaqueErrorFunctions = TokenTree.of(
      evalTemplateResource(
        getClass(),
        "runtimes/rust/conversions/error_common.rs",
        variables
      )
    );
    return new RustFile(
      rootPathForShape(service).resolve("conversions").resolve("error.rs"),
      TokenTree.of(modulesDeclarations, toDafnyOpaqueErrorFunctions, sdkContent)
    );
  }

  protected Set<RustFile> allStructureConversionModules() {
    return streamStructuresToGenerateStructsFor()
      .map(this::structureConversionModule)
      .collect(Collectors.toSet());
  }

  @Override
  protected boolean shouldGenerateStructForStructure(
    StructureShape structureShape
  ) {
    return (
      super.shouldGenerateStructForStructure(structureShape) &&
      !isInputOrOutputStructure(structureShape) &&
      // TODO: Filter to shapes in the service closure (this one's an example of an orphan)
      !structureShape
        .getId()
        .equals(
          ShapeId.from(
            "com.amazonaws.dynamodb#KinesisStreamingDestinationInput"
          )
        ) &&
      !structureShape
        .getId()
        .equals(
          ShapeId.from(
            "com.amazonaws.dynamodb#KinesisStreamingDestinationOutput"
          )
        )
    );
  }

  protected Set<RustFile> allEnumConversionModules() {
    return ModelUtils
      .streamEnumShapes(model, service.getId().getNamespace())
      .map(this::enumConversionModule)
      .collect(Collectors.toSet());
  }

  protected Set<RustFile> allErrorConversionModules() {
    return allErrorShapes()
      .map(this::errorConversionModule)
      .collect(Collectors.toSet());
  }

  protected Set<RustFile> allUnionConversionModules() {
    return model
      .getUnionShapes()
      .stream()
      .filter(this::shouldGenerateEnumForUnion)
      .map(this::unionConversionModule)
      .collect(Collectors.toSet());
  }

  @Override
  protected TokenTree operationRequestToDafnyFunction(
    final Shape bindingShape,
    final OperationShape operationShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(bindingShape, operationShape)
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
        ) -> ::dafny_runtime::Rc<
            crate::r#$dafnyTypesModuleName:L::$operationInputName:L,
        >{
            ::dafny_runtime::Rc::new(crate::r#$dafnyTypesModuleName:L::$operationInputName:L::$operationInputName:L {
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
      (operationIndex.isOutputStructure(parent) &&
        ((!targetShape.hasTrait(BoxTrait.class) &&
            (targetShape.isIntegerShape() || targetShape.isLongShape())) ||
          targetShape.isListShape())) ||
      (!operationIndex.isInputStructure(parent) &&
        targetShape.isBooleanShape() &&
        targetShape.hasTrait(DefaultTrait.class)) ||
      // TODO: I'm giving up on figuring out these ones for now
      SPECIAL_CASE_REQUIRED_MEMBERS.contains(member.getId())
    );
  }

  private static final Set<ShapeId> SPECIAL_CASE_REQUIRED_MEMBERS = Set.of(
    ShapeId.from("com.amazonaws.dynamodb#ImportTableDescription$ErrorCount"),
    ShapeId.from(
      "com.amazonaws.dynamodb#ImportTableDescription$ProcessedItemCount"
    ),
    ShapeId.from(
      "com.amazonaws.dynamodb#ImportTableDescription$ImportedItemCount"
    )
  );

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
    final Shape bindingShape,
    final OperationShape operationShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(bindingShape, operationShape)
    );
    StructureShape inputShape = model.expectShape(
      operationShape.getInputShape(),
      StructureShape.class
    );
    variables.put(
      "fluentMemberSetters",
      fluentMemberSettersForStructure(inputShape).toString()
    );
    variables.put("unwrapIfNecessary", ".unwrap()");

    return TokenTree.of(
      evalTemplate(
        """
        #[allow(dead_code)]
        pub fn from_dafny(
            dafny_value: ::dafny_runtime::Rc<
                crate::r#$dafnyTypesModuleName:L::$operationInputName:L,
            >
        ) -> $sdkCrate:L::operation::$snakeCaseOperationName:L::$sdkOperationInputStruct:L {
            $sdkCrate:L::operation::$snakeCaseOperationName:L::$sdkOperationInputStruct:L::builder()
                  $fluentMemberSetters:L
                  .build()
                  $unwrapIfNecessary:L
        }
        """,
        variables
      )
    );
  }

  @Override
  protected TokenTree operationResponseToDafnyFunction(
    final Shape bindingShape,
    final OperationShape operationShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(bindingShape, operationShape)
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
  }

  @Override
  protected TokenTree operationResponseFromDafnyFunction(
    final Shape bindingShape,
    final OperationShape operationShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(bindingShape, operationShape)
    );
    StructureShape outputShape = model.expectShape(
      operationShape.getOutputShape(),
      StructureShape.class
    );
    variables.put(
      "fluentMemberSetters",
      fluentMemberSettersForStructure(outputShape).toString()
    );
    final boolean needsUnwrap = outputShape
      .members()
      .stream()
      .anyMatch(memberShape ->
        memberShape.hasTrait(RequiredTrait.class) &&
        !model.expectShape(memberShape.getTarget()).isStructureShape()
      );
    variables.put("unwrapIfNecessary", needsUnwrap ? ".unwrap()" : "");

    return TokenTree.of(
      evalTemplate(
        """
        #[allow(dead_code)]
        pub fn from_dafny(
            dafny_value: ::dafny_runtime::Rc<
                crate::r#$dafnyTypesModuleName:L::$operationOutputName:L,
            >
        ) -> $sdkCrate:L::operation::$snakeCaseOperationName:L::$sdkOperationOutputStruct:L {
            $sdkCrate:L::operation::$snakeCaseOperationName:L::$sdkOperationOutputStruct:L::builder()
                  $fluentMemberSetters:L
                  .build()
                  $unwrapIfNecessary:L

        }
        """,
        variables
      )
    );
  }

  @Override
  protected TokenTree operationErrorConversionFunctions(
    final BoundOperationShape boundOperationShape
  ) {
    return operationErrorToDafnyFunction(
      boundOperationShape.bindingShape(),
      boundOperationShape.operationShape()
    );
  }

  protected TokenTree operationErrorToDafnyFunction(
    final Shape bindingShape,
    final OperationShape operationShape
  ) {
    TokenTree errorCases = TokenTree
      .of(
        operationShape
          .getErrors()
          .stream()
          .map(id ->
            errorVariantToDafny(
              bindingShape,
              operationShape,
              model.expectShape(id, StructureShape.class)
            )
          )
      )
      .lineSeparated();

    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(bindingShape, operationShape)
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
        ) -> ::dafny_runtime::Rc<crate::r#$dafnyTypesModuleName:L::Error> {
            match value {
              $sdkCrate:L::error::SdkError::ServiceError(service_error) => match service_error.err() {
                $errorCases:L
                e => {
                  let msg = format!("{:?}", e);
                  $rustRootModuleName:L::conversions::error::to_opaque_error(msg)
                }
              },
              _ => {
                let msg = format!("{:?}", value);
                $rustRootModuleName:L::conversions::error::to_opaque_error(msg)
              }
           }
        }

        """,
        variables
      )
    );
  }

  private RustFile typesErrorModule() {
    final Map<String, String> variables = serviceVariables();
    final String directErrorVariants = allErrorShapes()
      .map(errorShape ->
        evalTemplate(
          """
          $rustErrorName:L {
              error: $sdkCrate:L::types::error::$rustErrorName:L,
          },
          """,
          MapUtils.merge(variables, errorVariables(errorShape))
        )
      )
      .collect(Collectors.joining("\n\n"));
    variables.put("modeledErrorVariants", directErrorVariants);

    final String content = evalTemplateResource(
      getClass(),
      "runtimes/rust/types/error_awssdk.rs",
      variables
    );

    final Path path = rootPathForShape(service)
      .resolve("types")
      .resolve("error.rs");

    return new RustFile(path, TokenTree.of(content));
  }

  protected TokenTree errorVariantToDafny(
    final Shape bindingShape,
    final OperationShape operationShape,
    final StructureShape errorShape
  ) {
    final Map<String, String> variables = MapUtils.merge(
      serviceVariables(),
      operationVariables(bindingShape, operationShape)
    );
    String errorName = toPascalCase(errorShape.getId().getName());
    variables.put("errorName", errorName);
    variables.put(
      "snakeCaseErrorName",
      toSnakeCase(errorShape.getId().getName())
    );

    return TokenTree.of(
      evalTemplate(
        """
                $sdkCrate:L::operation::$snakeCaseOperationName:L::$operationName:LError::$errorName:L(e) =>
                    $rustRootModuleName:L::conversions::error::$snakeCaseErrorName:L::to_dafny(e.clone()),
        """,
        variables
      )
    );
  }

  private RustFile errorConversionModule(final StructureShape errorStructure) {
    String structureName = errorStructure.getId().getName();
    String snakeCaseName = toSnakeCase(structureName);
    String pascalCaseName = toPascalCase(structureName);
    Path path = rootPathForShape(service)
      .resolve("conversions")
      .resolve("error")
      .resolve(snakeCaseName + ".rs");
    String template =
      """
      #[allow(dead_code)]
      pub fn to_dafny(
          value: $rustTypesModuleName:L::error::$pascalCaseName:L,
      ) -> ::dafny_runtime::Rc<crate::r#$dafnyTypesModuleName:L::Error>{
        ::dafny_runtime::Rc::new(
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

  protected String getDafnyInternalModuleName(final String namespace) {
    return "software::amazon::cryptography::services::%s::internaldafny".formatted(
        getSdkId().toLowerCase()
      );
  }

  protected String getRustTypesModuleName() {
    return "%s::types".formatted(getSdkCrate());
  }

  @Override
  protected String getSdkId() {
    return service.expectTrait(ServiceTrait.class).getSdkId();
  }

  private String getSdkCrate() {
    return "aws_sdk_%s".formatted(getSdkId().toLowerCase(Locale.ROOT));
  }

  @Override
  protected HashMap<String, String> serviceVariables() {
    final HashMap<String, String> variables = super.serviceVariables();
    variables.put("sdkCrate", getSdkCrate());
    variables.put("clientName", "%sClient".formatted(getSdkId()));
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
    final Shape bindingShape,
    final OperationShape operationShape
  ) {
    final HashMap<String, String> variables = super.operationVariables(
      bindingShape,
      operationShape
    );
    variables.put(
      "operationInputType",
      rustTypeForShape(operationIndex.getInputShape(operationShape).get())
    );
    variables.put(
      "operationOutputType",
      rustTypeForShape(operationIndex.getOutputShape(operationShape).get())
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
    final String rootRustModuleName = getRustRootModuleName(
      service.getId().getNamespace()
    );
    return switch (shape.getType()) {
      case STRING, ENUM -> {
        if (shape.hasTrait(EnumTrait.class) || shape.isEnumShape()) {
          var enumShapeName = toSnakeCase(shape.toShapeId().getName());
          if (isDafnyOption) {
            yield TokenTree.of(
              """
              ::dafny_runtime::Rc::new(match &%s {
                  Some(x) => crate::_Wrappers_Compile::Option::Some { value: %s::conversions::%s::to_dafny(x.clone()) },
                  None => crate::_Wrappers_Compile::Option::None { }
              })
              """.formatted(rustValue, rootRustModuleName, enumShapeName)
            );
          } else if (isRustOption) {
            yield TokenTree.of(
              "%s::conversions::%s::to_dafny(%s.clone().unwrap())".formatted(
                  rootRustModuleName,
                  enumShapeName,
                  rustValue
                )
            );
          } else {
            yield TokenTree.of(
              "%s::conversions::%s::to_dafny(%s.clone())".formatted(
                  rootRustModuleName,
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
          yield TokenTree.of(
            "::dafny_runtime::Rc::new(%s)".formatted(valueToDafny)
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
              "crate::standard_library_conversions::obool_to_dafny(&Some(%s))".formatted(
                  rustValue
                )
            );
          }
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
          if (isRustOption) {
            yield TokenTree.of("%s.unwrap()".formatted(rustValue));
          } else {
            yield TokenTree.of(rustValue);
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
              "crate::standard_library_conversions::olong_to_dafny(&Some(%s))".formatted(
                  rustValue
                )
            );
          }
        } else {
          yield TokenTree.of(rustValue);
        }
      }
      case DOUBLE -> {
        if (isDafnyOption) {
          if (isRustOption) {
            yield TokenTree.of(
              "crate::standard_library_conversions::odouble_to_dafny(&%s)".formatted(
                  rustValue
                )
            );
          } else {
            yield TokenTree.of(
              "crate::standard_library_conversions::double_to_dafny(&Some(%s))".formatted(
                  rustValue
                )
            );
          }
        } else {
          yield TokenTree.of(
            "crate::standard_library_conversions::double_to_dafny(%s.clone())".formatted(
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
        var structureShapeName = toSnakeCase(shape.getId().getName());
        if (!isDafnyOption) {
          if (isRustOption) {
            yield TokenTree.of(
              """
              %s::conversions::%s::to_dafny(&%s.clone().unwrap())
              """.formatted(rootRustModuleName, structureShapeName, rustValue)
            );
          } else {
            yield TokenTree.of(
              """
              %s::conversions::%s::to_dafny(%s)
              """.formatted(rootRustModuleName, structureShapeName, rustValue)
            );
          }
        } else {
          yield TokenTree.of(
            """
            ::dafny_runtime::Rc::new(match &%s {
                Some(x) => crate::_Wrappers_Compile::Option::Some { value: %s::conversions::%s::to_dafny(x) },
                None => crate::_Wrappers_Compile::Option::None { }
            })
            """.formatted(rustValue, rootRustModuleName, structureShapeName)
          );
        }
      }
      default -> throw new IllegalArgumentException(
        "Unsupported shape type: %s".formatted(shape.getType())
      );
    };
  }

  @Override
  public TokenTree topLevelModuleDeclarations() {
    return TokenTree.of(
      """
      pub mod client;
      pub mod conversions;
      pub mod types;
      """
    );
  }

  protected String qualifiedRustStructureType(
    final StructureShape structureShape
  ) {
    if (operationIndex.isInputStructure(structureShape)) {
      final OperationShape operationShape = operationIndex
        .getInputBindings(structureShape)
        .stream()
        .collect(MoreCollectors.onlyElement());
      return (
        getSdkCrate() +
        "::operation::%s::%s".formatted(
            toSnakeCase(operationShape.getId().getName()),
            sdkOperationInputStruct(operationShape)
          )
      );
    }
    if (operationIndex.isOutputStructure(structureShape)) {
      final OperationShape operationShape = operationIndex
        .getOutputBindings(structureShape)
        .stream()
        .collect(MoreCollectors.onlyElement());
      return (
        getSdkCrate() +
        "::operation::%s::%s".formatted(
            toSnakeCase(operationShape.getId().getName()),
            sdkOperationOutputStruct(operationShape)
          )
      );
    }
    return super.qualifiedRustStructureType(structureShape);
  }

  protected String getRustConversionsModuleNameForShape(final Shape shape) {
    final String namespace = shape.getId().getNamespace();
    if (shape.isStructureShape()) {
      if (operationIndex.isInputStructure(shape)) {
        final OperationShape operationShape = operationIndex
          .getInputBindings(shape)
          .stream()
          .collect(MoreCollectors.onlyElement());
        return (
          getRustRootModuleName(namespace) +
          "::conversions::%s::_%s".formatted(
              toSnakeCase(operationName(operationShape)),
              toSnakeCase(syntheticOperationInputName(operationShape))
            )
        );
      }
      if (operationIndex.isOutputStructure(shape)) {
        final OperationShape operationShape = operationIndex
          .getOutputBindings(shape)
          .stream()
          .collect(MoreCollectors.onlyElement());
        return (
          getRustRootModuleName(namespace) +
          "::conversions::%s::_%s".formatted(
              toSnakeCase(operationName(operationShape)),
              toSnakeCase(syntheticOperationOutputName(operationShape))
            )
        );
      }
    }

    return super.getRustConversionsModuleNameForShape(shape);
  }
}
