// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithygo;

import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;

public class LocalServiceGenerator implements ShapeGenerator<ServiceShape> {
    private Model model;
    private final GoDelegator writerDelegator;
    private SymbolProvider symbolProvider;

    public LocalServiceGenerator(GoDelegator writerDelegator, Model model, SymbolProvider symbolProvider) {
        this.writerDelegator = writerDelegator;
        this.model = model;
        this.symbolProvider = symbolProvider;
    }

    @Override
    public void generate(ServiceShape service) {
        // Generate each operation for the service. We do this here instead of via the operation visitor method to
        // limit it to the operations bound to the service.
        Symbol serviceSymbol = symbolProvider.toSymbol(service);
        LocalServiceTrait serviceTrait = service.expectTrait(LocalServiceTrait.class);
        Symbol configSymbol = symbolProvider.toSymbol(model.expectShape(serviceTrait.getConfigId()));
        writerDelegator.useShapeWriter(service, goWriter -> {
            String namespace = service.toShapeId().getNamespace().replace(".", "");
            goWriter.addImport(String.format("%sinternaldafnytypes", namespace), "");
            goWriter.addImport(String.format("%sinternaldafny", namespace), "");
            goWriter.addImport("types","");
            goWriter.addImport("typeconversion","");
            goWriter.addImport("context","");

            goWriter.write("type $T struct {", serviceSymbol);

            goWriter.write("clientConfig $T", configSymbol);
            goWriter.write("}");

            goWriter.write("func NewClient(clientConfig $T) (*$T, error) {", configSymbol, serviceSymbol);
            goWriter.write("client := &$T { clientConfig }", serviceSymbol);
            goWriter.write("return client, nil");
            goWriter.write("}");

            service.getAllOperations().forEach(operation -> {
                String operationName = operation.getName();
                String inputType = model.expectShape(model.expectShape(operation).asOperationShape().get().getInputShape()).toShapeId().getName();
                String outputType = model.expectShape(model.expectShape(operation).asOperationShape().get().getOutputShape()).toShapeId().getName();
                goWriter.write("func (client *$T) $L(ctx context.Context, params types.$L) (types.$L, error) {", serviceSymbol, operationName, inputType, outputType);
                goWriter.write("""
                                       	var dafnyType, _ = typeconversion.FromNativeToDafny$L(params)
                                       	result, _ := $Linternaldafny.New_$LClient_().$L(dafnyType).Extract().($Linternaldafnytypes.$L)
                                        var nativeType, _ = typeconversion.FromDafnyToNative$L(result)
                                       	return nativeType, nil
                                       }
                                       """,
                               inputType, namespace, serviceTrait.getSdkId(), operationName, namespace, outputType, outputType
                               );
            });

            new StructureGenerator(model, symbolProvider, writerDelegator).generate(model.expectShape(serviceTrait.getConfigId()).asStructureShape().get());
        });
    }
}
