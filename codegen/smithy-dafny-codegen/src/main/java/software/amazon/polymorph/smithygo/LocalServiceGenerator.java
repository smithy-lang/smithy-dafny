// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithygo;

import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.codegen.ImportDeclarations;
import software.amazon.polymorph.smithygo.codegen.SmithyGoDependency;
import software.amazon.polymorph.smithygo.codegen.StructureGenerator;
import software.amazon.polymorph.smithygo.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithygo.shapevisitor.DafnyToSmithyShapeVisitor;
import software.amazon.polymorph.smithygo.shapevisitor.SmithyToDafnyShapeVisitor;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.traits.ErrorTrait;

import java.util.function.Function;


public class LocalServiceGenerator implements Runnable {
    private final GenerationContext context;
    private final ServiceShape service;

    public LocalServiceGenerator(GenerationContext context, ServiceShape service) {
        this.context = context;
        this.service = service;
    }

    @Override
    public void run() {
        context.writerDelegator().useShapeWriter(service, this::generateService);
    }

    private void generateService(GoWriter writer) {
        generateClient(writer);
        generateShim();
        generateUnmodelledErrors(context);
    }
    void generateClient(GoWriter writer) {
        // Generate each operation for the service. We do this here instead of via the operation visitor method to
        // limit it to the operations bound to the service.
        var symbolProvider = context.symbolProvider();
        var model = context.model();
        var serviceSymbol = context.symbolProvider().toSymbol(service);
        final LocalServiceTrait serviceTrait = service.expectTrait(LocalServiceTrait.class);
        var configSymbol = symbolProvider.toSymbol(model.expectShape(serviceTrait.getConfigId()));
        context.writerDelegator().useFileWriter("types/types.go", writer1 -> {
                                                    new StructureGenerator(model, symbolProvider, writer1, model.expectShape(serviceTrait.getConfigId()).asStructureShape().get()).run();
                                                });

        writer.addImport(DafnyNameResolver.dafnyTypesNamespace(context.settings()));
        writer.addImport(DafnyNameResolver.dafnyNamespace(context.settings()));
        writer.addImport("types");
        writer.addImport("context");
        var dafnyClient = DafnyNameResolver.getDafnyClient(context.settings(), serviceTrait.getSdkId());
        writer.write("""
                             type $T struct {
                                 dafnyClient *$L
                             }
                                                                 
                             func NewClient(clientConfig $T) (*$T, error) {
                                 var dafnyConfig = $L(clientConfig)
                                 var dafny_response = $L(dafnyConfig)
                                 if (dafny_response.Is_Failure()) {
                                      panic("Client construction failed. This should never happen")
                                 }
                                 var dafnyClient = dafny_response.Extract().(*$L)
                                 client := &$T { dafnyClient }
                                 return client, nil
                             }
                             """,
                     serviceSymbol, dafnyClient , configSymbol, serviceSymbol,DafnyNameResolver.getInputToDafnyMethodName(context, serviceTrait.getConfigId()), DafnyNameResolver.createDafnyClient(context.settings(), serviceTrait.getSdkId()), dafnyClient, serviceSymbol);

        service.getAllOperations().forEach(operation -> {
            final OperationShape operationShape = model.expectShape(operation, OperationShape.class);
            final Shape inputShape = model.expectShape(operationShape.getInputShape());
            final Shape outputShape = model.expectShape(operationShape.getOutputShape());
            final String inputType = model.expectShape(model.expectShape(operation).asOperationShape().get().getInputShape()).toShapeId().getName();
            final String outputType = model.expectShape(model.expectShape(operation).asOperationShape().get().getOutputShape()).toShapeId().getName();
            final Function<String, String> checkErrorClass = (String x) -> {
                return """
                                               if err.Is_$L() {
                                               return nil, $L_Output_FromDafny(err.Get().($L.Error_$L))
                                           }
                        """.formatted(x, x, x);
            };
            writer.write("""
                                   func (client *$T) $L(ctx context.Context, params types.$L) (*types.$L, error) {
                                       var dafny_request $L = $L(params)
                                       var dafny_response = client.dafnyClient.$L(dafny_request)
                                       if (dafny_response.Is_Failure()) {
                                           err := dafny_response.Dtor_error().($L.Error);
                                           ${C|}
                                           if err.Is_CollectionOfErrors() {
                                               return nil, CollectionOfErrors_Output_FromDafny(err)
                                           }
                                           if err.Is_Opaque() {
                                               return nil, OpaqueError_Output_FromDafny(err)
                                           }
                                       }
                                       var native_response = $L(dafny_response.Extract().($L))
                                       return &native_response, nil
                                   }
                                 """,
                         serviceSymbol,
                         operationShape.getId().getName(),
                         inputType, outputType,
                         DafnyNameResolver.getDafnyType(context.settings(), symbolProvider.toSymbol(inputShape)),
                         DafnyNameResolver.getInputToDafnyMethodName(context, operationShape),
                         operationShape.getId().getName(),
                         DafnyNameResolver.dafnyTypesNamespace(context.settings()),
                         writer.consumer( w -> {
                             for (var errorShape :
                                     model.getShapesWithTrait(ErrorTrait.class)) {
                                 w.write("""
                                                                             if err.Is_$L() {
                                                                             return nil, $L_Output_FromDafny(err)
                                                                         }
                                                      """, errorShape.toShapeId().getName(), errorShape.toShapeId().getName());
                             }
                         }),
                         DafnyNameResolver.getOutputFromDafnyMethodName(context, operationShape), DafnyNameResolver.getDafnyType(context.settings(), symbolProvider.toSymbol(outputShape)));
        });
    }

    void generateShim() {
        var symbolProvider = context.symbolProvider();
        var model = context.model();
        final LocalServiceTrait serviceTrait = service.expectTrait(LocalServiceTrait.class);
        var configSymbol = symbolProvider.toSymbol(model.expectShape(serviceTrait.getConfigId()));
        var namespace = "%swrapped".formatted(DafnyNameResolver.dafnyNamespace(context.settings()));
        context.writerDelegator().useFileWriter("shim.go", namespace, writer -> {
            writer.addImport(DafnyNameResolver.dafnyTypesNamespace(context.settings()));
            writer.addImport("Wrappers");
            writer.addImport("context");
            writer.addImport("types");
            writer.addImport(DafnyNameResolver.serviceNamespace(service));

            writer.write("""
                                 type Shim struct {
                                     $L
                                     client *$L.Client
                                 }
                                 """,
                         DafnyNameResolver.getDafnyInterfaceClient(context.settings(), serviceTrait.getSdkId()),
                         DafnyNameResolver.serviceNamespace(service)
            );
            writer.write("""
                                                   
                                 func Wrapped$L(inputConfig $L) Wrappers.Result {
                                     var nativeConfig = $L.$L(inputConfig)
                                     var nativeClient, nativeError = $L.NewClient(nativeConfig)
                                     if nativeError != nil {
                                        return Wrappers.Companion_Result_.Create_Failure_($L.Companion_Error_.Create_Opaque_(nativeError))
                                     }
                                     return Wrappers.Companion_Result_.Create_Success_(&Shim{client: nativeClient})
                                 }
                                 """,
                         serviceTrait.getSdkId(), DafnyNameResolver.getDafnyType(context.settings(), configSymbol),
                         DafnyNameResolver.serviceNamespace(service),
                         DafnyNameResolver.getOutputFromDafnyMethodName(context, serviceTrait.getConfigId()),
                         DafnyNameResolver.serviceNamespace(service), DafnyNameResolver.dafnyTypesNamespace(context.settings())
            );

            service.getAllOperations().forEach(operation -> {
                final OperationShape operationShape = model.expectShape(operation, OperationShape.class);
                final Shape inputShape = model.expectShape(operationShape.getInputShape());
                final Shape outputShape = model.expectShape(operationShape.getOutputShape());
                final String inputType = model.expectShape(model.expectShape(operation).asOperationShape().get().getInputShape()).toShapeId().getName();
                final String outputType = model.expectShape(model.expectShape(operation).asOperationShape().get().getOutputShape()).toShapeId().getName();
                writer.write("""
                                       func (shim *Shim) $L(input $L) Wrappers.Result {
                                           var native_request = $L.$L(input)
                                           var native_response, native_error = shim.client.$L(context.Background(), native_request)
                                           if native_error != nil {
                                               switch native_error.(type) {
                                                ${C|}
                                                case types.CollectionOfErrors:
                                                    return Wrappers.Companion_Result_.Create_Failure_($L.CollectionOfErrors_Input_ToDafny(native_error.(types.CollectionOfErrors)))
                                                default:
                                                    return Wrappers.Companion_Result_.Create_Failure_($L.OpaqueError_Input_ToDafny(native_error.(types.OpaqueError)))
                                                }
                                           }
                                           var dafny_response = $L.$L(*native_response)
                                           return Wrappers.Companion_Result_.Create_Success_(dafny_response)
                                       }
                                     """,
                             operationShape.getId().getName(),
                             DafnyNameResolver.getDafnyType(context.settings(), symbolProvider.toSymbol(inputShape)),
                             DafnyNameResolver.serviceNamespace(service),
                             DafnyNameResolver.getInputFromDafnyMethodName(context, operationShape),
                             operationShape.getId().getName(),
                             writer.consumer(w -> c(w)),
                             DafnyNameResolver.serviceNamespace(service),
                             DafnyNameResolver.serviceNamespace(service),
                             DafnyNameResolver.serviceNamespace(service),
                             DafnyNameResolver.getOutputToDafnyMethodName(context, operationShape));
            });
        });
    }

    void c(GoWriter writer) {
        for (Shape error:
             context.model().getShapesWithTrait(ErrorTrait.class)) {
            writer.write("""
                                 case types.$L:
                                      return Wrappers.Companion_Result_.Create_Failure_($L.$L_Input_ToDafny(native_error.(types.$L)))
                                           
                                                
                                 """, context.symbolProvider().toSymbol(error).getName(), DafnyNameResolver.serviceNamespace(context.settings().getService(context.model())), context.symbolProvider().toSymbol(error).getName(), context.symbolProvider().toSymbol(error).getName());
        }
    }

    void generateUnmodelledErrors(GenerationContext context) {
        context.writerDelegator().useFileWriter("types/unmodelled_errors.go", "types", writer -> {
            writer.addUseImports(SmithyGoDependency.FMT);
            writer.write("""
                                 type CollectionOfErrors struct {
                                     ListOfErrors []error
                                     Message string
                                 }
                                 
                                 func (e CollectionOfErrors) Error() string {
                                 	return fmt.Sprintf("message: %s\\n err %v", e.Message, e.ListOfErrors)
                                 }
                                 
                                 type OpaqueError struct {
                                    ErrObject interface{}
                                 }
                                 
                                 func (e OpaqueError) Error() string {
                                    return fmt.Sprintf("message: %v", e.ErrObject )
                                 }
                                 """);
        });
    }
}
