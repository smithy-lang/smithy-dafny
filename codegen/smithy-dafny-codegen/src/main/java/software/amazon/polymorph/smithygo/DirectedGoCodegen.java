package software.amazon.polymorph.smithygo;

import software.amazon.polymorph.smithygo.integration.GoIntegration;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.codegen.core.directed.CreateContextDirective;
import software.amazon.smithy.codegen.core.directed.CreateSymbolProviderDirective;
import software.amazon.smithy.codegen.core.directed.DirectedCodegen;
import software.amazon.smithy.codegen.core.directed.GenerateEnumDirective;
import software.amazon.smithy.codegen.core.directed.GenerateErrorDirective;
import software.amazon.smithy.codegen.core.directed.GenerateIntEnumDirective;
import software.amazon.smithy.codegen.core.directed.GenerateServiceDirective;
import software.amazon.smithy.codegen.core.directed.GenerateStructureDirective;
import software.amazon.smithy.codegen.core.directed.GenerateUnionDirective;
import software.amazon.smithy.model.knowledge.TopDownIndex;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;

import java.util.Set;
import java.util.TreeSet;
import java.util.logging.Logger;

public class DirectedGoCodegen implements DirectedCodegen<GoCodegenContext, GoSettings, GoIntegration> {

    private static final Logger LOGGER = Logger.getLogger(DirectedGoCodegen.class.getName());
    @Override
    public SymbolProvider createSymbolProvider(CreateSymbolProviderDirective<GoSettings> directive) {
        return new SymbolVisitor(directive.model(), directive.settings());
    }

    @Override
    public GoCodegenContext createContext(CreateContextDirective<GoSettings, GoIntegration> directive) {
        return GoCodegenContext.builder()
                                       .model(directive.model())
                                       .settings(directive.settings())
                                       .symbolProvider(directive.symbolProvider())
                                       .fileManifest(directive.fileManifest())
                                       .integrations(directive.integrations())
                                       .writerDelegator(new GoDelegator(directive.fileManifest(), directive.symbolProvider()))
                                       .build();
    }

    @Override
    public void generateService(GenerateServiceDirective<GoCodegenContext, GoSettings> directive) {
        // Write API client type and utilities.
        directive.context().writerDelegator().useShapeWriter(directive.service(), serviceWriter -> {
            ServiceShape service = directive.service();
            // Generate each operation for the service. We do this here instead of via the operation visitor method to
            // limit it to the operations bound to the service.
            TopDownIndex topDownIndex = directive.model().getKnowledge(TopDownIndex.class);
            Set<OperationShape> containedOperations = new TreeSet<>(topDownIndex.getContainedOperations(service));
            for (OperationShape operation : containedOperations) {
                Symbol operationSymbol = directive.symbolProvider().toSymbol(operation);

                directive.context().writerDelegator().useShapeWriter(
                        operation, operationWriter -> new OperationGenerator(directive.settings(), directive.model(), directive.symbolProvider(),
                                                                             operationWriter, service, operation, operationSymbol).run());
            }
        });

    }

    @Override
    public void generateStructure(GenerateStructureDirective<GoCodegenContext, GoSettings> directive) {

    }

    @Override
    public void generateError(GenerateErrorDirective<GoCodegenContext, GoSettings> directive) {

    }

    @Override
    public void generateUnion(GenerateUnionDirective<GoCodegenContext, GoSettings> directive) {

    }

    @Override
    public void generateEnumShape(GenerateEnumDirective<GoCodegenContext, GoSettings> directive) {

    }

    @Override
    public void generateIntEnumShape(GenerateIntEnumDirective<GoCodegenContext, GoSettings> directive) {

    }
}
