// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithygo;

import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.polymorph.smithygo.codegen.StructureGenerator;
import software.amazon.polymorph.smithygo.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithygo.shapevisitor.DafnyToSmithyShapeVisitor;
import software.amazon.polymorph.smithygo.shapevisitor.SmithyToDafnyShapeVisitor;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;


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
                                 DafnyClient *$L
                             }
                                                                 
                             func NewClient(clientConfig $T) (*$T, error) {
                                 var dafnyConfig = $L(clientConfig)
                                 var response = $L(dafnyConfig)
                                 var dafnyClient = response.Extract().(*$L)
                                 client := &$T { dafnyClient }
                                 return client, nil
                             }
                             """,
                     serviceSymbol, dafnyClient , configSymbol, serviceSymbol,DafnyNameResolver.getToDafnyMethodName(context, serviceTrait.getConfigId()), DafnyNameResolver.createDafnyClient(context.settings(), serviceTrait.getSdkId()), dafnyClient, serviceSymbol);

        service.getAllOperations().forEach(operation -> {
            final OperationShape operationShape = model.expectShape(operation, OperationShape.class);
            final Shape inputShape = model.expectShape(operationShape.getInputShape());
            final Shape outputShape = model.expectShape(operationShape.getOutputShape());
            final String inputType = model.expectShape(model.expectShape(operation).asOperationShape().get().getInputShape()).toShapeId().getName();
            final String outputType = model.expectShape(model.expectShape(operation).asOperationShape().get().getOutputShape()).toShapeId().getName();
            writer.write("""
                                   func (client *$T) $L(ctx context.Context, params types.$L) (*types.$L, error) {
                                       var dafny_request $L = $L(params)
                                       var dafny_response = client.DafnyClient.$L(dafny_request)
                                       var native_response = $L(dafny_response.Extract().($L))
                                       return &native_response, nil
                                   }
                                 """,
                         serviceSymbol,
                         operationShape.getId().getName(),
                         inputType, outputType,
                         DafnyNameResolver.getDafnyType(context.settings(), symbolProvider.toSymbol(inputShape)),
                         DafnyNameResolver.getToDafnyMethodName(context, operationShape),
                         operationShape.getId().getName(),
                         DafnyNameResolver.getFromDafnyMethodName(context, operationShape), DafnyNameResolver.getDafnyType(context.settings(), symbolProvider.toSymbol(outputShape)));
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
            writer.addImport(DafnyNameResolver.serviceNamespace(service));

            writer.write("""                   
                                                                         func Wrapped$L(inputConfig $L) (Wrappers.Result) {
                                                                             var nativeConfig = $L.$L(inputConfig)
                                                                             var nativeClient, _ = $L.NewClient(nativeConfig)
                                                                             return Wrappers.Companion_Result_.Create_Success_(nativeClient.DafnyClient)
                                                                         }
                                                                         """,
                                                                 serviceTrait.getSdkId(), DafnyNameResolver.getDafnyType(context.settings(), configSymbol), DafnyNameResolver.serviceNamespace(service), DafnyNameResolver.getFromDafnyMethodName(context, serviceTrait.getConfigId()), DafnyNameResolver.serviceNamespace(service));
                                                });
    }
}
