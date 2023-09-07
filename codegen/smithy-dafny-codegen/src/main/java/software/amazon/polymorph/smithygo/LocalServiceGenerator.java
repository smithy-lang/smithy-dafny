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
import software.amazon.smithy.model.traits.UnitTypeTrait;

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
            final String inputType = inputShape.hasTrait(UnitTypeTrait.class) ? "" : ", params types.%s".formatted(inputShape.toShapeId().getName());
            final String outputType = outputShape.hasTrait(UnitTypeTrait.class) ? "" : "*types.%s,".formatted(outputShape.toShapeId().getName());

            String baseClientCall;
            if (inputShape.hasTrait(UnitTypeTrait.class)) {
                baseClientCall = "var dafny_response = client.dafnyClient.%s()".formatted(operationShape.getId().getName());
            } else {
                baseClientCall = """
                        var dafny_request %s = %s(params)
                        var dafny_response = client.dafnyClient.%s(dafny_request)
                        """.formatted(DafnyNameResolver.getDafnyType(context.settings(), symbolProvider.toSymbol(inputShape)),
                                      DafnyNameResolver.getInputToDafnyMethodName(context, operationShape), operationShape.getId().getName());
            }

            String returnResponse, returnError;
            if (outputShape.hasTrait(UnitTypeTrait.class)) {
                returnResponse = "return nil";
                returnError = "return";
            } else {
                returnResponse = """
                        var native_response = %s(dafny_response.Extract().(%s))
                        return &native_response, nil
                        """.formatted(DafnyNameResolver.getOutputFromDafnyMethodName(context, operationShape),
                                      DafnyNameResolver.getDafnyType(context.settings(), symbolProvider.toSymbol(outputShape)));
                returnError = "return nil,";
            }


            writer.write("""
                                   func (client *$T) $L(ctx context.Context $L) ($L error) {
                                       $L
                                       if (dafny_response.Is_Failure()) {
                                           err := dafny_response.Dtor_error().($L.Error);
                                           ${C|}
                                           if err.Is_CollectionOfErrors() {
                                               $L CollectionOfErrors_Output_FromDafny(err)
                                           }
                                           if err.Is_Opaque() {
                                               $L OpaqueError_Output_FromDafny(err)
                                           }
                                       }
                                       $L
                                   }
                                 """,
                         serviceSymbol,
                         operationShape.getId().getName(),
                         inputType, outputType,
                         baseClientCall,
                         DafnyNameResolver.dafnyTypesNamespace(context.settings()),
                         writer.consumer( w -> {
                             for (var errorShape :
                                     model.getShapesWithTrait(ErrorTrait.class)) {
                                 w.write("""
                                                                             if err.Is_$L() {
                                                                             $L $L_Output_FromDafny(err)
                                                                         }
                                                      """, errorShape.toShapeId().getName(), returnError, errorShape.toShapeId().getName());
                             }
                         }),returnError, returnError, returnResponse
                         );
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
                final String inputType = inputShape.hasTrait(UnitTypeTrait.class) ? "" : "input %s".formatted(DafnyNameResolver.getDafnyType(context.settings(), symbolProvider.toSymbol(inputShape)));
                final String outputType = outputShape.hasTrait(UnitTypeTrait.class) ? "" : "*types.%s,".formatted(outputShape.toShapeId().getName());

                final String typeConversion = inputShape.hasTrait(UnitTypeTrait.class) ? "" : "var native_request = %s.%s(input)".formatted(DafnyNameResolver.serviceNamespace(service),
                                                                                                                                      DafnyNameResolver.getInputFromDafnyMethodName(context, operationShape));
                final String clientCall =  "shim.client.%s(context.Background() %s)".formatted(operationShape.getId().getName(), inputShape.hasTrait(UnitTypeTrait.class) ? "" : ", native_request");
                String clientResponse, returnResponse;
                if (outputShape.hasTrait(UnitTypeTrait.class)) {
                    clientResponse = "var native_error";
                    returnResponse = "dafny.TupleOf()";
                    writer.addImport("dafny");
                } else {
                    clientResponse = "var native_response, native_error";
                    returnResponse = "%s.%s(*native_response)".formatted(DafnyNameResolver.serviceNamespace(service),
                                                                         DafnyNameResolver.getOutputToDafnyMethodName(context, operationShape));
                }
                writer.write("""
                                       func (shim *Shim) $L($L) Wrappers.Result {
                                           $L
                                           $L = $L
                                           if native_error != nil {
                                               switch native_error.(type) {
                                                ${C|}
                                                case types.CollectionOfErrors:
                                                    return Wrappers.Companion_Result_.Create_Failure_($L.CollectionOfErrors_Input_ToDafny(native_error.(types.CollectionOfErrors)))
                                                default:
                                                    return Wrappers.Companion_Result_.Create_Failure_($L.OpaqueError_Input_ToDafny(native_error.(types.OpaqueError)))
                                                }
                                           }
                                           return Wrappers.Companion_Result_.Create_Success_($L)
                                       }
                                     """,
                             operationShape.getId().getName(),
                             inputType, typeConversion, clientResponse, clientCall,
                             writer.consumer(w -> c(w)),
                             DafnyNameResolver.serviceNamespace(service),
                             DafnyNameResolver.serviceNamespace(service),
                             returnResponse
                             );
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
