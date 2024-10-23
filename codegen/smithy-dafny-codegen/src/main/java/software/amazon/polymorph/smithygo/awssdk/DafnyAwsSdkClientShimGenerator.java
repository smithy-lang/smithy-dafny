package software.amazon.polymorph.smithygo.awssdk;

import static software.amazon.polymorph.smithygo.utils.Constants.DAFNY_RUNTIME_GO_LIBRARY_MODULE;

import software.amazon.polymorph.smithygo.codegen.AddOperationShapes;
import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoDelegator;
import software.amazon.polymorph.smithygo.codegen.SmithyGoDependency;
import software.amazon.polymorph.smithygo.localservice.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithygo.localservice.nameresolver.SmithyNameResolver;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.traits.UnitTypeTrait;

public class DafnyAwsSdkClientShimGenerator implements Runnable {

  private final GenerationContext context;
  private final ServiceShape service;
  private final GoDelegator writerDelegator;
  private final Model dafnyNonNormalizedModel;
  private final Model awsNormalizedModel;
  private final SymbolProvider symbolProvider;

  public DafnyAwsSdkClientShimGenerator(
    GenerationContext context,
    ServiceShape service
  ) {
    this.context = context;
    this.service = service;
    dafnyNonNormalizedModel = context.model();
    awsNormalizedModel =
      AddOperationShapes.execute(context.model(), service.toShapeId());
    writerDelegator = context.writerDelegator();
    symbolProvider = context.symbolProvider();
  }

  @Override
  public void run() {
    generateShim();
  }

  void generateShim() {
    final var namespace =
      "%swrapped".formatted(
          DafnyNameResolver.dafnyNamespace(
            service.expectTrait(ServiceTrait.class)
          )
        );

    writerDelegator.useFileWriter(
      "%s/shim.go".formatted(namespace),
      namespace,
      writer -> {
        writer.addImportFromModule(
          SmithyNameResolver.getGoModuleNameForSmithyNamespace(
            context.settings().getService().getNamespace()
          ),
          DafnyNameResolver.dafnyTypesNamespace(service)
        );
        writer.addImport(
          SmithyNameResolver.getGoModuleNameForSdkNamespace(
            awsNormalizedModel
              .expectShape(service.toShapeId(), ServiceShape.class)
              .toShapeId()
              .getNamespace()
          )
        );
        writer.addImportFromModule(
          "github.com/dafny-lang/DafnyStandardLibGo",
          "Wrappers"
        );
        writer.addUseImports(SmithyGoDependency.CONTEXT);
        writer.addImportFromModule(
          SmithyNameResolver.getGoModuleNameForSmithyNamespace(
            context.settings().getService().getNamespace()
          ),
          SmithyNameResolver.shapeNamespace(service)
        );
        writer.write(
          """
          type Shim struct {
              $L
              Client *$L
          }
          """,
          DafnyNameResolver.getDafnyInterfaceClient(
            service,
            service.expectTrait(ServiceTrait.class)
          ),
          SmithyNameResolver.getAwsServiceClient(
            service.expectTrait(ServiceTrait.class)
          )
        );

        service
          .getOperations()
          .forEach(operation -> {
            final var awsNormalizedOperation = awsNormalizedModel.expectShape(
              operation,
              OperationShape.class
            );
            final var awsNormalizedInputShape = awsNormalizedModel.expectShape(
              awsNormalizedOperation.getInputShape()
            );
            final var awsNormalizedOutputShape = awsNormalizedModel.expectShape(
              awsNormalizedOperation.getOutputShape()
            );

            final var operationShape = dafnyNonNormalizedModel.expectShape(
              operation,
              OperationShape.class
            );
            final var inputShape = dafnyNonNormalizedModel.expectShape(
              operationShape.getInputShape()
            );
            final var outputShape = dafnyNonNormalizedModel.expectShape(
              operationShape.getOutputShape()
            );
            final var inputType = awsNormalizedInputShape.hasTrait(
                UnitTypeTrait.class
              )
              ? ""
              : "input %s".formatted(
                  DafnyNameResolver.getDafnyType(
                    inputShape,
                    symbolProvider.toSymbol(inputShape)
                  )
                );

            final var typeConversion = awsNormalizedInputShape.hasTrait(
                UnitTypeTrait.class
              )
              ? ""
              : "var native_request = %s(input)".formatted(
                  SmithyNameResolver.getFromDafnyMethodName(
                    awsNormalizedInputShape,
                    ""
                  )
                );

            final var clientCall =
              "shim.Client.%s(context.Background() %s)".formatted(
                  operationShape.getId().getName(),
                  awsNormalizedInputShape.hasTrait(UnitTypeTrait.class)
                    ? ""
                    : ", &native_request"
                );

            String clientResponse, returnResponse;
            if (awsNormalizedOutputShape.hasTrait(UnitTypeTrait.class)) {
              clientResponse = "var _, native_error";
              returnResponse = "dafny.TupleOf()";
              writer.addImportFromModule(
                DAFNY_RUNTIME_GO_LIBRARY_MODULE,
                "dafny"
              );
            } else {
              clientResponse = "var native_response, native_error";
              returnResponse =
                "%s(*native_response)".formatted(
                    SmithyNameResolver.getToDafnyMethodName(
                      awsNormalizedOutputShape,
                      ""
                    )
                  );
            }

            writer.write(
              """
                func (shim *Shim) $L($L) Wrappers.Result {
                    $L
                    $L = $L
                    if native_error != nil {
                        return Wrappers.Companion_Result_.Create_Failure_($L.Error_ToDafny(native_error))
                    }
                    return Wrappers.Companion_Result_.Create_Success_($L)
                }
              """,
              operationShape.getId().getName(),
              inputType,
              typeConversion,
              clientResponse,
              clientCall,
              SmithyNameResolver.shapeNamespace(service),
              returnResponse
            );
          });
      }
    );
  }
}
