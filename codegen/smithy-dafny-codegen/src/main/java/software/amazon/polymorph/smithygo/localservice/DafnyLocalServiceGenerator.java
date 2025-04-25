// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithygo.localservice;

import static software.amazon.polymorph.smithygo.codegen.SymbolUtils.POINTABLE;
import static software.amazon.polymorph.smithygo.utils.Constants.DAFNY_RUNTIME_GO_LIBRARY_MODULE;
import static software.amazon.polymorph.smithygo.utils.Constants.SMITHY_DAFNY_STD_LIB_GO;

import java.util.LinkedHashSet;
import java.util.stream.Collectors;
import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoDelegator;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.codegen.SmithyGoDependency;
import software.amazon.polymorph.smithygo.codegen.SymbolUtils;
import software.amazon.polymorph.smithygo.codegen.UnionGenerator;
import software.amazon.polymorph.smithygo.localservice.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithygo.localservice.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithygo.utils.Constants;
import software.amazon.polymorph.smithygo.utils.GoCodegenUtils;
import software.amazon.polymorph.traits.ExtendableTrait;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.knowledge.TopDownIndex;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.UnitTypeTrait;

public class DafnyLocalServiceGenerator implements Runnable {

  private final GenerationContext context;
  private final ServiceShape service;
  private final TopDownIndex topDownIndex;
  private final GoDelegator writerDelegator;
  private final Model model;
  private final SymbolProvider symbolProvider;

  public DafnyLocalServiceGenerator(
    GenerationContext context,
    ServiceShape service
  ) {
    this.context = context;
    this.service = service;
    model = context.model();
    topDownIndex = TopDownIndex.of(model);
    writerDelegator = context.writerDelegator();
    symbolProvider = context.symbolProvider();
  }

  @Override
  public void run() {
    writerDelegator.useShapeWriter(service, this::generateService);
  }

  private void generateService(GoWriter writer) {
    if (service.hasTrait(LocalServiceTrait.class)) {
      generateClient(writer);
      generateUnmodelledErrors(context);
      generateReferencedResources(context);
    }
    generateShim();
  }

  void generateClient(GoWriter writer) {
    // Generate each operation for the service. We do this here instead of via the operation visitor method to
    // limit it to the operations bound to the service.
    final var serviceSymbol = symbolProvider.toSymbol(service);
    final var serviceTrait = service.expectTrait(LocalServiceTrait.class);
    final var configSymbol = symbolProvider.toSymbol(
      model.expectShape(serviceTrait.getConfigId())
    );

    writerDelegator.useFileWriter(
      "%s/types.go".formatted(
          SmithyNameResolver.smithyTypesNamespace(service, model)
        ),
      SmithyNameResolver.smithyTypesNamespace(service, model),
      writer1 -> {
        model
          .getUnionShapes()
          .stream()
          .filter(unionShape ->
            unionShape
              .getId()
              .getNamespace()
              .equals(service.getId().getNamespace())
          )
          .sorted()
          .forEach(unionShape -> {
            new UnionGenerator(model, symbolProvider, unionShape)
              .generateUnion(writer1);
          });
      }
    );

    writer.addImportFromModule(
      SmithyNameResolver.getGoModuleNameForSmithyNamespace(
        context.settings().getService().getNamespace()
      ),
      DafnyNameResolver.dafnyTypesNamespace(service)
    );
    writer.addImportFromModule(
      SmithyNameResolver.getGoModuleNameForSmithyNamespace(
        context.settings().getService().getNamespace()
      ),
      DafnyNameResolver.dafnyNamespace(serviceTrait)
    );
    writer.addImportFromModule(
      SmithyNameResolver.getGoModuleNameForSmithyNamespace(
        context.settings().getService().getNamespace()
      ),
      SmithyNameResolver.smithyTypesNamespace(service, model)
    );
    writer.addUseImports(SmithyGoDependency.CONTEXT);
    var configShape = configSymbol.expectProperty(
      SymbolUtils.SHAPE,
      Shape.class
    );
    if (
      !configShape
        .toShapeId()
        .getNamespace()
        .equals(service.toShapeId().getNamespace())
    ) {
      writer.addImportFromModule(
        SmithyNameResolver.getGoModuleNameForSmithyNamespace(
          configShape.toShapeId().getNamespace()
        ),
        SmithyNameResolver.smithyTypesNamespace(configShape, model)
      );
      writer.addImportFromModule(
        SmithyNameResolver.getGoModuleNameForSmithyNamespace(
          configShape.toShapeId().getNamespace()
        ),
        SmithyNameResolver.shapeNamespace(configShape)
      );
    }
    final var dafnyClient = DafnyNameResolver.getDafnyInterfaceClient(service);
    writer.write(
      """
      type $T struct {
          DafnyClient $L
      }

      func NewClient(clientConfig $L) (*$T, error) {
          var dafnyConfig = $L(clientConfig)
          var dafny_response = $L(dafnyConfig)
          if (dafny_response.Is_Failure()) {
               panic("Client construction failed. This should never happen")
          }
          var dafnyClient = dafny_response.Extract().($L)
          client := &$T { dafnyClient }
          return client, nil
      }
      """,
      serviceSymbol,
      dafnyClient,
      SmithyNameResolver.getSmithyType(configShape, configSymbol, model),
      serviceSymbol,
      SmithyNameResolver.getToDafnyMethodName(
        service,
        context.model().expectShape(serviceTrait.getConfigId()),
        ""
      ),
      DafnyNameResolver.createDafnyClient(service, serviceTrait.getSdkId()),
      dafnyClient,
      serviceSymbol
    );

    service
      .getOperations()
      .forEach(operation -> {
        final var operationShape = model.expectShape(
          operation,
          OperationShape.class
        );
        var inputShape = model.expectShape(operationShape.getInputShape());
        writer.addImportFromModule(
          SmithyNameResolver.getGoModuleNameForSmithyNamespace(
            inputShape.toShapeId().getNamespace()
          ),
          DafnyNameResolver.dafnyTypesNamespace(inputShape)
        );
        if (
          !inputShape
            .toShapeId()
            .getNamespace()
            .equals(service.toShapeId().getNamespace())
        ) {
          writer.addImportFromModule(
            SmithyNameResolver.getGoModuleNameForSmithyNamespace(
              inputShape.toShapeId().getNamespace()
            ),
            SmithyNameResolver.shapeNamespace(inputShape)
          );
        }
        var outputShape = model.expectShape(operationShape.getOutputShape());
        writer.addImportFromModule(
          SmithyNameResolver.getGoModuleNameForSmithyNamespace(
            outputShape.toShapeId().getNamespace()
          ),
          SmithyNameResolver.smithyTypesNamespace(outputShape, model)
        );
        if (
          !outputShape
            .toShapeId()
            .getNamespace()
            .equals(service.toShapeId().getNamespace())
        ) {
          writer.addImportFromModule(
            SmithyNameResolver.getGoModuleNameForSmithyNamespace(
              outputShape.toShapeId().getNamespace()
            ),
            SmithyNameResolver.shapeNamespace(outputShape)
          );
        }
        var inputType = inputShape.hasTrait(UnitTypeTrait.class)
          ? ""
          : ", params %s.%s".formatted(
              SmithyNameResolver.smithyTypesNamespace(inputShape, model),
              inputShape.toShapeId().getName()
            );
        var outputType = outputShape.hasTrait(UnitTypeTrait.class)
          ? ""
          : "*%s.%s,".formatted(
              SmithyNameResolver.smithyTypesNamespace(outputShape, model),
              outputShape.toShapeId().getName()
            );
        String baseClientCall;
        if (inputShape.hasTrait(UnitTypeTrait.class)) {
          baseClientCall =
            "var dafny_response = client.DafnyClient.%s()".formatted(
                operationShape.getId().getName()
              );
        } else {
          final String toDafnyMethod;
          if (inputShape.hasTrait(PositionalTrait.class)) {
            // TODO: We can probably refactor this for better code quality. Like: inputForPositional could be redundant and we could use input itself.
            final MemberShape inputMemberShapeForPositional = inputShape
              .getAllMembers()
              .values()
              .stream()
              .findFirst()
              .get();
            inputShape =
              model.expectShape(inputMemberShapeForPositional.getTarget());
            toDafnyMethod =
              Constants.funcNameGenerator(
                inputMemberShapeForPositional,
                "ToDafny"
              );
            inputType =
              ", params %s".formatted(
                  SmithyNameResolver.getSmithyType(
                    inputShape,
                    symbolProvider.toSymbol(inputShape),
                    model
                  )
                );
          } else {
            toDafnyMethod =
              SmithyNameResolver.getToDafnyMethodName(service, inputShape, "");
          }
          baseClientCall =
            """
            var dafny_request %s = %s(params)
            var dafny_response = client.DafnyClient.%s(dafny_request)
            """.formatted(
                DafnyNameResolver.getDafnyType(
                  inputShape,
                  symbolProvider.toSymbol(inputShape)
                ),
                // We could unwrap the shape right here if positional but we will also have to change shim
                // TODO: Decide this later
                toDafnyMethod,
                operationShape.getId().getName()
              );
        }

        final String returnResponse, returnError;
        if (outputShape.hasTrait(UnitTypeTrait.class)) {
          returnResponse = "return nil";
          returnError = "return";
        } else {
          if (outputShape.hasTrait(PositionalTrait.class)) {
            final MemberShape postionalMemShape = outputShape
              .getAllMembers()
              .values()
              .stream()
              .findFirst()
              .get();
            outputShape = model.expectShape(postionalMemShape.getTarget());
            if (outputShape.hasTrait(ReferenceTrait.class)) {
              outputShape =
                model.expectShape(
                  outputShape.expectTrait(ReferenceTrait.class).getReferentId()
                );
            }
            final String fromDafnyConvMethodName = outputShape.isResourceShape()
              ? SmithyNameResolver.getFromDafnyMethodName(
                service,
                outputShape,
                ""
              )
              : Constants.funcNameGenerator(postionalMemShape, "FromDafny");
            outputType =
              SmithyNameResolver
                .getSmithyType(
                  outputShape,
                  symbolProvider.toSymbol(outputShape),
                  model
                )
                .concat(",");
            GoCodegenUtils.importNamespace(outputShape, writer);
            returnResponse =
              """
              var native_response = %s(dafny_response.Dtor_value().(%s))
              return native_response, nil
              """.formatted(
                  fromDafnyConvMethodName,
                  DafnyNameResolver.getDafnyType(
                    outputShape,
                    symbolProvider.toSymbol(outputShape)
                  )
                );
            returnError =
              """
              var defaultVal %s
              return defaultVal,""".formatted(
                  SmithyNameResolver.getSmithyType(
                    outputShape,
                    symbolProvider.toSymbol(outputShape),
                    model
                  )
                );
          } else {
            writer.addImportFromModule(
              SmithyNameResolver.getGoModuleNameForSmithyNamespace(
                outputShape.toShapeId().getNamespace()
              ),
              DafnyNameResolver.dafnyTypesNamespace(outputShape)
            );
            returnResponse =
              """
              var native_response = %s(dafny_response.Dtor_value().(%s))
              return &native_response, nil
              """.formatted(
                  SmithyNameResolver.getFromDafnyMethodName(
                    service,
                    outputShape,
                    ""
                  ),
                  DafnyNameResolver.getDafnyType(
                    outputShape,
                    symbolProvider.toSymbol(outputShape)
                  )
                );
            returnError = "return nil,";
          }
        }
        String validationCheck = "";
        // inputShape is not a structure only when we have a positional trait
        // TODO: Figure out how to validate constraint in a structure with positional trait
        if (
          !inputShape.hasTrait(UnitTypeTrait.class) &&
          inputShape.isStructureShape()
        ) {
          validationCheck =
            """
                err := params.Validate()
                if err != nil {
                  opaqueErr := %s.OpaqueError{
                    ErrObject: err,
                  }
                  %s opaqueErr
                }
            """.formatted(
                SmithyNameResolver.smithyTypesNamespace(inputShape, model),
                returnError
              );
        }

        writer.write(
          """
            func (client *$T) $L(ctx context.Context $L) ($L error) {
                $L
                $L
                if (dafny_response.Is_Failure()) {
                    err := dafny_response.Dtor_error().($L.Error);
                    $L Error_FromDafny(err)
                }
                $L
            }
          """,
          serviceSymbol,
          operationShape.getId().getName(),
          inputType,
          outputType,
          validationCheck,
          baseClientCall,
          DafnyNameResolver.dafnyTypesNamespace(service),
          returnError,
          returnResponse
        );
      });
  }

  void generateShim() {
    final var namespace =
      "Wrapped%sService".formatted(DafnyNameResolver.dafnyNamespace(service));

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
        writer.addImportFromModule(SMITHY_DAFNY_STD_LIB_GO, "Wrappers");
        writer.addImportFromModule(
          SmithyNameResolver.getGoModuleNameForSmithyNamespace(
            context.settings().getService().getNamespace()
          ),
          SmithyNameResolver.smithyTypesNamespace(service, model)
        );
        writer.addUseImports(SmithyGoDependency.CONTEXT);
        writer.addImportFromModule(
          SmithyNameResolver.getGoModuleNameForSmithyNamespace(
            context.settings().getService().getNamespace()
          ),
          SmithyNameResolver.shapeNamespace(service)
        );

        if (service.hasTrait(LocalServiceTrait.class)) {
          final var serviceTrait = service.expectTrait(LocalServiceTrait.class);
          final var configShape = model.expectShape(serviceTrait.getConfigId());
          final var configSymbol = symbolProvider.toSymbol(configShape);

          writer.write(
            """
            type Shim struct {
                $L
                client *$L.Client
            }
            """,
            DafnyNameResolver.getDafnyInterfaceClient(service),
            SmithyNameResolver.shapeNamespace(service)
          );

          writer.addImportFromModule(DAFNY_RUNTIME_GO_LIBRARY_MODULE, "dafny");

          writer.write(
            """
            func (_static *CompanionStruct_Default___) Wrapped$L(inputConfig $L) Wrappers.Result {
                var nativeConfig = $L.$L(inputConfig)
                var nativeClient, nativeError = $L.NewClient(nativeConfig)
                if nativeError != nil {
                   return Wrappers.Companion_Result_.Create_Failure_($L.Companion_Error_.Create_Opaque_(nativeError))
                }
                return Wrappers.Companion_Result_.Create_Success_(&Shim{client: nativeClient})
            }
            """,
            serviceTrait.getSdkId(),
            DafnyNameResolver.getDafnyType(configShape, configSymbol),
            SmithyNameResolver.shapeNamespace(
              model.expectShape(serviceTrait.getConfigId())
            ),
            SmithyNameResolver.getFromDafnyMethodName(
              service,
              model.expectShape(serviceTrait.getConfigId()),
              ""
            ),
            SmithyNameResolver.shapeNamespace(service),
            DafnyNameResolver.dafnyTypesNamespace(service)
          );
        }

        service
          .getOperations()
          .forEach(operation -> {
            final var operationShape = model.expectShape(
              operation,
              OperationShape.class
            );
            var inputShape = model.expectShape(operationShape.getInputShape());
            var outputShape = model.expectShape(
              operationShape.getOutputShape()
            );
            var isMemberShapePointable = true;
            String toDafnyConvMethodName =
              SmithyNameResolver.getToDafnyMethodName(outputShape, "");
            if (outputShape.hasTrait(PositionalTrait.class)) {
              // Shape with positional shape MUST have only one membershape.
              // We are considering the memberShape inside positional shape should be required.
              // TODO: Change isMemberShapePointable if we decide otherwise in https://github.com/smithy-lang/smithy-dafny/issues/727
              isMemberShapePointable = false;
              final MemberShape postionalMemShape = outputShape
                .getAllMembers()
                .values()
                .stream()
                .findFirst()
                .get();
              outputShape = model.expectShape(postionalMemShape.getTarget());
              if (outputShape.hasTrait(ReferenceTrait.class)) {
                outputShape =
                  model.expectShape(
                    outputShape
                      .expectTrait(ReferenceTrait.class)
                      .getReferentId()
                  );
              }
              toDafnyConvMethodName =
                outputShape.isResourceShape()
                  ? SmithyNameResolver.getToDafnyMethodName(outputShape, "")
                  : SmithyNameResolver
                    .shapeNamespace(postionalMemShape)
                    .concat(".")
                    .concat(
                      Constants.funcNameGenerator(postionalMemShape, "ToDafny")
                    );
            }
            // this is maybe because positional trait can change this
            final var maybeInputType = inputShape.hasTrait(UnitTypeTrait.class)
              ? ""
              : "input %s".formatted(
                  DafnyNameResolver.getDafnyType(
                    inputShape,
                    symbolProvider.toSymbol(inputShape)
                  )
                );

            final String inputType;
            final String inputToClient;
            if (inputShape.hasTrait(UnitTypeTrait.class)) {
              inputToClient = "";
            } else {
              inputToClient = ", native_request";
            }
            final var clientCall =
              "shim.client.%s(context.Background() %s)".formatted(
                  operationShape.getId().getName(),
                  inputToClient
                );
            final String clientResponse, returnResponse;
            if (outputShape.hasTrait(UnitTypeTrait.class)) {
              clientResponse = "var native_error";
              returnResponse = "dafny.TupleOf()";
              writer.addImportFromModule(
                DAFNY_RUNTIME_GO_LIBRARY_MODULE,
                "dafny"
              );
            } else {
              clientResponse = "var native_response, native_error";
              returnResponse =
                "%s(%snative_response)".formatted(
                    toDafnyConvMethodName,
                    isMemberShapePointable ? "*" : ""
                  );
            }
            var fromDafnyConvMethodName =
              SmithyNameResolver.getFromDafnyMethodName(inputShape, "");
            if (inputShape.hasTrait(PositionalTrait.class)) {
              writer.addImportFromModule(
                DAFNY_RUNTIME_GO_LIBRARY_MODULE,
                "dafny"
              );
              final MemberShape postionalMemShape = inputShape
                .getAllMembers()
                .values()
                .stream()
                .findFirst()
                .get();
              inputShape = model.expectShape(postionalMemShape.getTarget());
              if (inputShape.hasTrait(ReferenceTrait.class)) {
                inputShape =
                  model.expectShape(
                    inputShape.expectTrait(ReferenceTrait.class).getReferentId()
                  );
              }
              fromDafnyConvMethodName =
                SmithyNameResolver
                  .shapeNamespace(postionalMemShape)
                  .concat(".")
                  .concat(
                    Constants.funcNameGenerator(postionalMemShape, "FromDafny")
                  );
              final Symbol symbolForPositional = symbolProvider.toSymbol(
                inputShape
              );
              final String dafnyType = DafnyNameResolver.getDafnyType(
                inputShape,
                symbolForPositional
              );
              inputType = "input %s".formatted(dafnyType);
            } else {
              inputType = maybeInputType;
            }
            final var typeConversion = inputShape.hasTrait(UnitTypeTrait.class)
              ? ""
              : "var native_request = %s(input)".formatted(
                  fromDafnyConvMethodName
                );
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

  void shimErrors(GoWriter writer) {
    for (final var error : model
      .getShapesWithTrait(ErrorTrait.class)
      .stream()
      .sorted()
      .collect(Collectors.toCollection(LinkedHashSet::new))) {
      writer.write(
        """
        case $L.$L:
             return Wrappers.Companion_Result_.Create_Failure_($L(native_error.($L.$L)))


        """,
        SmithyNameResolver.smithyTypesNamespace(error, model),
        symbolProvider.toSymbol(error).getName(),
        SmithyNameResolver.getToDafnyMethodName(service, error, ""),
        SmithyNameResolver.smithyTypesNamespace(error, model),
        symbolProvider.toSymbol(error).getName()
      );
    }
  }

  void resourceErrors(GoWriter writer) {
    for (final var error : model
      .getShapesWithTrait(ErrorTrait.class)
      .stream()
      .sorted()
      .collect(Collectors.toCollection(LinkedHashSet::new))) {
      writer.write(
        """
        case $L:
             return Wrappers.Companion_Result_.Create_Failure_($L(native_error.($L)))


        """,
        SmithyNameResolver.getSmithyType(
          error,
          symbolProvider.toSymbol(error),
          model
        ),
        SmithyNameResolver.getToDafnyMethodName(service, error, ""),
        SmithyNameResolver.getSmithyType(
          error,
          symbolProvider.toSymbol(error),
          model
        )
      );
    }
  }

  void generateUnmodelledErrors(GenerationContext context) {
    writerDelegator.useFileWriter(
      "%s/types.go".formatted(
          SmithyNameResolver.smithyTypesNamespace(service, model)
        ),
      SmithyNameResolver.smithyTypesNamespace(service, model),
      writer -> {
        writer.write(
          """
          type $LBaseException interface {
              // This is a dummy method to allow type assertion since Go empty interfaces
              // aren't useful for type assertion checks. No concrete class is expected to implement
              // this method. This is also not exported.
              interfaceBindingMethod()
          }
          """,
          service.toShapeId().getName()
        );
      }
    );
    writerDelegator.useFileWriter(
      "%s/unmodelled_errors.go".formatted(
          SmithyNameResolver.smithyTypesNamespace(service, model)
        ),
      SmithyNameResolver.smithyTypesNamespace(service, model),
      writer -> {
        writer.addUseImports(SmithyGoDependency.FMT);
        writer.write(
          """
          type CollectionOfErrors struct {
              $LBaseException
              ListOfErrors []error
              Message string
          }

          func (e CollectionOfErrors) Error() string {
          	return fmt.Sprintf("message: %s\\n err %v", e.Message, e.ListOfErrors)
          }

          type OpaqueError struct {
             $LBaseException
             ErrObject interface{}
          }

          func (e OpaqueError) Error() string {
             return fmt.Sprintf("message: %v", e.ErrObject )
          }
          """,
          service.toShapeId().getName(),
          service.toShapeId().getName()
        );
      }
    );
  }

  void generateReferencedResources(final GenerationContext context) {
    final var refResources = model
      .getShapesWithTrait(ReferenceTrait.class)
      .stream()
      .sorted()
      .collect(Collectors.toCollection(LinkedHashSet::new));
    for (final var refResource : refResources) {
      if (!refResource.expectTrait(ReferenceTrait.class).isService()) {
        final var resource = refResource
          .expectTrait(ReferenceTrait.class)
          .getReferentId();
        final var resourceShape = model.expectShape(resource);

        if (
          !service.toShapeId().getNamespace().equals(resource.getNamespace())
        ) {
          continue;
        }
        writerDelegator.useFileWriter(
          "%s/types.go".formatted(
              SmithyNameResolver.smithyTypesNamespace(service, model)
            ),
          SmithyNameResolver.smithyTypesNamespace(service, model),
          writer -> {
            writer.write(
              """
              type I$L interface {
              ${C|}
              }
              """,
              resource.getName(),
              writer.consumer(w -> {
                model
                  .expectShape(resource, ResourceShape.class)
                  .getOperations()
                  .forEach(operation -> {
                    final var operationShape = model.expectShape(
                      operation,
                      OperationShape.class
                    );
                    final var input =
                      GoCodegenUtils.getOperationalShapeInputName(
                        model,
                        operationShape,
                        symbolProvider
                      );
                    final var output =
                      GoCodegenUtils.getOperationalShapeOutputName(
                        model,
                        operationShape,
                        symbolProvider
                      );
                    w.write(
                      """
                      $L($L) ($L error)
                      """,
                      operationShape.getId().getName(),
                      input,
                      // If output is not empty append the `,` to separate return types
                      output.isEmpty() ? "" : output.concat(",")
                    );
                  });
              })
            );
          }
        );

        if (
          model
            .expectShape(resource, ResourceShape.class)
            .hasTrait(ExtendableTrait.class)
        ) {
          generateNativeResourceWrapper(
            context,
            model.expectShape(resource, ResourceShape.class)
          );
        }

        writerDelegator.useFileWriter(
          "%s/%s.go".formatted(
              SmithyNameResolver.shapeNamespace(service),
              resource.getName()
            ),
          SmithyNameResolver.shapeNamespace(service),
          writer -> {
            writer.addImportFromModule(
              SmithyNameResolver.getGoModuleNameForSmithyNamespace(
                context.settings().getService().getNamespace()
              ),
              SmithyNameResolver.smithyTypesNamespace(service, model)
            );
            writer.addImportFromModule(
              SmithyNameResolver.getGoModuleNameForSmithyNamespace(
                resource.getNamespace()
              ),
              DafnyNameResolver.dafnyTypesNamespace(resourceShape)
            );
            writer.write(
              """
              type %s struct {
                  Impl %s.I%s
              }
              """.formatted(
                  resource.getName(),
                  DafnyNameResolver.dafnyTypesNamespace(resourceShape),
                  resource.getName()
                )
            );

            model
              .expectShape(resource, ResourceShape.class)
              .getOperations()
              .forEach(operation -> {
                final var operationShape = model.expectShape(
                  operation,
                  OperationShape.class
                );
                var inputShape = model.expectShape(
                  operationShape.getInputShape()
                );

                var outputShape = model.expectShape(
                  operationShape.getOutputShape()
                );
                final String inputType;
                var outputType = outputShape.hasTrait(UnitTypeTrait.class)
                  ? ""
                  : "*%s,".formatted(
                      SmithyNameResolver.getSmithyType(
                        outputShape,
                        symbolProvider.toSymbol(outputShape),
                        model
                      )
                    );

                final String baseClientCall;
                if (inputShape.hasTrait(UnitTypeTrait.class)) {
                  baseClientCall =
                    "var dafny_response = this.Impl.%s()".formatted(
                        operationShape.getId().getName()
                      );
                  inputType = "";
                } else {
                  if (inputShape.hasTrait(PositionalTrait.class)) {
                    inputShape =
                      model.expectShape(
                        inputShape
                          .getAllMembers()
                          .values()
                          .stream()
                          .findFirst()
                          .get()
                          .getTarget()
                      );
                  }
                  inputType =
                    "params %s".formatted(
                        SmithyNameResolver.getSmithyType(
                          inputShape,
                          symbolProvider.toSymbol(inputShape),
                          model
                        )
                      );
                  baseClientCall =
                    """
                    var dafny_request %s = %s(params)
                    var dafny_response = this.Impl.%s(dafny_request)
                    """.formatted(
                        DafnyNameResolver.getDafnyType(
                          inputShape,
                          symbolProvider.toSymbol(inputShape)
                        ),
                        SmithyNameResolver.getToDafnyMethodName(
                          service,
                          inputShape,
                          ""
                        ),
                        operationShape.getId().getName()
                      );
                }

                final String returnResponse, returnError;
                if (outputShape.hasTrait(UnitTypeTrait.class)) {
                  returnResponse = "return nil";
                  returnError = "return";
                } else {
                  if (outputShape.hasTrait(PositionalTrait.class)) {
                    final MemberShape postionalMemShape = outputShape
                      .getAllMembers()
                      .values()
                      .stream()
                      .findFirst()
                      .get();
                    outputShape =
                      model.expectShape(postionalMemShape.getTarget());
                    if (outputShape.hasTrait(ReferenceTrait.class)) {
                      outputShape =
                        model.expectShape(
                          outputShape
                            .expectTrait(ReferenceTrait.class)
                            .getReferentId()
                        );
                    }
                    final String fromDafnyConvMethodName =
                      outputShape.isResourceShape()
                        ? SmithyNameResolver.getFromDafnyMethodName(
                          service,
                          outputShape,
                          ""
                        )
                        : Constants.funcNameGenerator(
                          postionalMemShape,
                          "FromDafny"
                        );

                    outputType =
                      SmithyNameResolver
                        .getSmithyType(
                          outputShape,
                          symbolProvider.toSymbol(outputShape),
                          model
                        )
                        .concat(",");
                    final var typeAssertion = outputShape.isResourceShape()
                      ? ".(%s)".formatted(
                          DafnyNameResolver.getDafnyType(
                            outputShape,
                            symbolProvider.toSymbol(outputShape)
                          )
                        )
                      : "";
                    returnResponse =
                      """
                      var native_response = %s(dafny_response.Dtor_value()%s)
                      return %snative_response, nil
                      """.formatted(
                          fromDafnyConvMethodName,
                          typeAssertion,
                          // Currently we expect all the structure with positional shape to have required trait on its membershape.
                          // TODO: If this changed in https://github.com/smithy-lang/smithy-dafny/issues/727, we need to fix it.
                          outputShape.hasTrait(ServiceTrait.class) ? "*" : ""
                        );
                    returnError =
                      """
                      var defaultVal %s
                      return defaultVal,""".formatted(
                          SmithyNameResolver.getSmithyType(
                            outputShape,
                            symbolProvider.toSymbol(outputShape),
                            model
                          )
                        );
                  } else {
                    returnResponse =
                      """
                      var native_response = %s(dafny_response.Dtor_value().(%s))
                      return &native_response, nil
                      """.formatted(
                          SmithyNameResolver.getFromDafnyMethodName(
                            service,
                            outputShape,
                            ""
                          ),
                          DafnyNameResolver.getDafnyType(
                            inputShape,
                            symbolProvider.toSymbol(outputShape)
                          )
                        );
                    returnError = "return nil,";
                  }
                  GoCodegenUtils.importNamespace(outputShape, writer);
                }

                writer.write(
                  """
                    func (this *$L) $L($L) ($L error) {
                        $L
                        if (dafny_response.Is_Failure()) {
                            err := dafny_response.Dtor_error().($L.Error);
                            $L Error_FromDafny(err)
                        }
                        $L
                    }
                  """,
                  resource.getName(),
                  operationShape.getId().getName(),
                  inputType,
                  outputType,
                  baseClientCall,
                  DafnyNameResolver.dafnyTypesNamespace(service),
                  returnError,
                  returnResponse
                );
              });
          }
        );
      } else {
        // Generate Service
      }
    }
  }

  void generateNativeResourceWrapper(
    GenerationContext context,
    ResourceShape resourceShape
  ) {
    writerDelegator.useFileWriter(
      "%s/%sNativeWrapper.go".formatted(
          SmithyNameResolver.shapeNamespace(service),
          resourceShape.getId().getName()
        ),
      SmithyNameResolver.shapeNamespace(service),
      writer -> {
        writer.addImportFromModule(
          context.settings().getModuleName(),
          SmithyNameResolver.smithyTypesNamespace(service, model)
        );
        writer.addImportFromModule(SMITHY_DAFNY_STD_LIB_GO, "Wrappers");
        writer.addImportFromModule(
          SmithyNameResolver.getGoModuleNameForSmithyNamespace(
            resourceShape.toShapeId().getNamespace()
          ),
          DafnyNameResolver.dafnyTypesNamespace(resourceShape)
        );

        writer.write(
          """
          type %sNativeWrapper struct {
              %s.I%s
              Impl %s.I%s
          }
          """.formatted(
              resourceShape.getId().getName(),
              DafnyNameResolver.dafnyTypesNamespace(resourceShape),
              resourceShape.getId().getName(),
              SmithyNameResolver.smithyTypesNamespace(resourceShape, model),
              resourceShape.getId().getName()
            )
        );

        resourceShape
          .getOperations()
          .forEach(operation -> {
            final var operationShape = model.expectShape(
              operation,
              OperationShape.class
            );
            var inputShape = model.expectShape(operationShape.getInputShape());
            var outputShape = model.expectShape(
              operationShape.getOutputShape()
            );
            final var outputType = outputShape.hasTrait(UnitTypeTrait.class)
              ? ""
              : "*%s,".formatted(
                  SmithyNameResolver.getSmithyType(
                    outputShape,
                    symbolProvider.toSymbol(outputShape),
                    model
                  )
                );
            String fromDafnyConvMethodNameForInput =
              SmithyNameResolver.getFromDafnyMethodName(
                service,
                inputShape,
                ""
              );
            if (inputShape.hasTrait(PositionalTrait.class)) {
              final MemberShape postionalMemShape = inputShape
                .getAllMembers()
                .values()
                .stream()
                .findFirst()
                .get();
              inputShape = model.expectShape(postionalMemShape.getTarget());
              if (inputShape.hasTrait(ReferenceTrait.class)) {
                inputShape =
                  model.expectShape(
                    inputShape.expectTrait(ReferenceTrait.class).getReferentId()
                  );
              }
              fromDafnyConvMethodNameForInput =
                inputShape.isResourceShape()
                  ? SmithyNameResolver.getFromDafnyMethodName(
                    service,
                    inputShape,
                    ""
                  )
                  : Constants.funcNameGenerator(postionalMemShape, "FromDafny");
            }
            final var inputType = inputShape.hasTrait(UnitTypeTrait.class)
              ? ""
              : "input %s".formatted(
                  DafnyNameResolver.getDafnyType(
                    inputShape,
                    symbolProvider.toSymbol(inputShape)
                  )
                );
            final var typeConversion = inputShape.hasTrait(UnitTypeTrait.class)
              ? ""
              : "var native_request = %s(input)".formatted(
                  fromDafnyConvMethodNameForInput
                );
            final var clientCall =
              "this.Impl.%s(%s)".formatted(
                  operationShape.getId().getName(),
                  inputShape.hasTrait(UnitTypeTrait.class)
                    ? ""
                    : "native_request"
                );
            final String clientResponse, returnResponse;
            if (outputShape.hasTrait(UnitTypeTrait.class)) {
              clientResponse = "var native_error";
              returnResponse = "dafny.TupleOf()";
              writer.addImportFromModule(
                DAFNY_RUNTIME_GO_LIBRARY_MODULE,
                "dafny"
              );
            } else {
              String toDafnyConvMethodNameForOutput =
                SmithyNameResolver.getToDafnyMethodName(
                  service,
                  outputShape,
                  ""
                );
              boolean deReferenceRequired = true;
              boolean referenceType = false;
              if (outputShape.hasTrait(PositionalTrait.class)) {
                final MemberShape postionalMemShape = outputShape
                  .getAllMembers()
                  .values()
                  .stream()
                  .findFirst()
                  .get();
                outputShape = model.expectShape(postionalMemShape.getTarget());
                if (outputShape.hasTrait(ReferenceTrait.class)) {
                  outputShape =
                    model.expectShape(
                      outputShape
                        .expectTrait(ReferenceTrait.class)
                        .getReferentId()
                    );
                  // If shape is pointer type, we need to fetch its address
                  // because conversion function will have pointer as input
                  referenceType =
                    context
                      .symbolProvider()
                      .toSymbol(outputShape)
                      .getProperty(POINTABLE, Boolean.class)
                      .orElse(false);
                }
                toDafnyConvMethodNameForOutput =
                  outputShape.isResourceShape()
                    ? SmithyNameResolver.getToDafnyMethodName(
                      service,
                      outputShape,
                      ""
                    )
                    : Constants.funcNameGenerator(postionalMemShape, "ToDafny");
                deReferenceRequired = false;
              }
              clientResponse = "var native_response, native_error";
              returnResponse =
                "%s(%snative_response)".formatted(
                    toDafnyConvMethodNameForOutput,
                    deReferenceRequired ? "*" : (referenceType ? "&" : "")
                  );
            }
            writer.write(
              """
                func (this *$LNativeWrapper) $L($L) Wrappers.Result {
                    $L
                    $L = $L
                    if native_error != nil {
                        return Wrappers.Companion_Result_.Create_Failure_(Error_ToDafny(native_error))
                    }
                    return Wrappers.Companion_Result_.Create_Success_($L)
                }
              """,
              resourceShape.getId().getName(),
              operationShape.getId().getName(),
              inputType,
              typeConversion,
              clientResponse,
              clientCall,
              returnResponse
            );
          });
      }
    );
  }
}
