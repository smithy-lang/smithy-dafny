/*
 * Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

package software.amazon.polymorph.smithygo;

import software.amazon.smithy.codegen.core.CodegenException;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.knowledge.OperationIndex;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.DeprecatedTrait;
import software.amazon.smithy.model.traits.StreamingTrait;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;
import java.util.stream.Stream;

/**
 * Generates a client operation and associated custom shapes.
 */
public final class OperationGenerator implements Runnable {

    private final GoSettings settings;
    private final Model model;
    private final SymbolProvider symbolProvider;
    private final GoWriter writer;
    private final ServiceShape service;
    private final OperationShape operation;
    private final Symbol operationSymbol;

    public OperationGenerator(
            GoSettings settings,
            Model model,
            SymbolProvider symbolProvider,
            GoWriter writer,
            ServiceShape service,
            OperationShape operation,
            Symbol operationSymbol
    ) {
        this.settings = settings;
        this.model = model;
        this.symbolProvider = symbolProvider;
        this.writer = writer;
        this.service = service;
        this.operation = operation;
        this.operationSymbol = operationSymbol;
    }

    @Override
    public void run() {
        OperationIndex operationIndex = OperationIndex.of(model);
        Symbol serviceSymbol = symbolProvider.toSymbol(service);

        if (!operationIndex.getInput(operation).isPresent()) {
            // Theoretically this shouldn't ever get hit since we automatically insert synthetic inputs / outputs.
            throw new CodegenException(
                    "Operations are required to have input shapes in order to allow for future evolution.");
        }
        StructureShape inputShape = operationIndex.getInput(operation).get();
        Symbol inputSymbol = symbolProvider.toSymbol(inputShape);

        if (!operationIndex.getOutput(operation).isPresent()) {
            throw new CodegenException(
                    "Operations are required to have output shapes in order to allow for future evolution.");
        }
        StructureShape outputShape = operationIndex.getOutput(operation).get();
        Symbol outputSymbol = symbolProvider.toSymbol(outputShape);

        Symbol contextSymbol = SymbolUtils.createValueSymbolBuilder("Context", SmithyGoDependency.CONTEXT).build();
        writer.openBlock("func (c $P) $T(ctx $T, params $P, optFns ...func(*Options)) ($P, error) {", "}",
                serviceSymbol, operationSymbol, contextSymbol, inputSymbol, outputSymbol, () -> {
                    writer.write("if params == nil { params = &$T{} }", inputSymbol);
                    writer.write("");

                    writer.write("result, metadata, err := c.invokeOperation(ctx, $S, params, optFns)",
                            operationSymbol.getName());
                    writer.write("if err != nil { return nil, err }");
                    writer.write("");

                    writer.write("out := result.($P)", outputSymbol);
                    writer.write("out.ResultMetadata = metadata");
                    writer.write("return out, nil");
                }).write("");

        // Write out the input and output structures. These are written out here to prevent naming conflicts with other
        // shapes in the model.
        new StructureGenerator(model, symbolProvider, writer, service, inputShape, inputSymbol)
                .renderStructure(() -> {
                }, true);

        // The output structure gets a metadata member added.
        Symbol metadataSymbol = SymbolUtils.createValueSymbolBuilder("Metadata", SmithyGoDependency.SMITHY_MIDDLEWARE)
                .build();

        boolean hasEventStream = Stream.concat(inputShape.members().stream(),
                        outputShape.members().stream())
                .anyMatch(memberShape -> StreamingTrait.isEventStream(model, memberShape));

        new StructureGenerator(model, symbolProvider, writer, service, outputShape, outputSymbol)
                .renderStructure(() -> {
                    if (outputShape.getMemberNames().size() != 0) {
                        writer.write("");
                    }


                    writer.write("ResultMetadata $T", metadataSymbol);
                });
    }
}
