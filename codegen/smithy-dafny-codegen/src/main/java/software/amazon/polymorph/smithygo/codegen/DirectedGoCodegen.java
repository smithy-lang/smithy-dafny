package software.amazon.polymorph.smithygo.codegen;

import software.amazon.polymorph.smithygo.DafnyTypeConversionProtocol;
import software.amazon.polymorph.smithygo.LocalServiceGenerator;
import software.amazon.polymorph.smithygo.codegen.integration.GoIntegration;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.codegen.core.TopologicalIndex;
import software.amazon.smithy.codegen.core.directed.CreateContextDirective;
import software.amazon.smithy.codegen.core.directed.CreateSymbolProviderDirective;
import software.amazon.smithy.codegen.core.directed.DirectedCodegen;
import software.amazon.smithy.codegen.core.directed.GenerateEnumDirective;
import software.amazon.smithy.codegen.core.directed.GenerateErrorDirective;
import software.amazon.smithy.codegen.core.directed.GenerateIntEnumDirective;
import software.amazon.smithy.codegen.core.directed.GenerateServiceDirective;
import software.amazon.smithy.codegen.core.directed.GenerateStructureDirective;
import software.amazon.smithy.codegen.core.directed.GenerateUnionDirective;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.traits.InputTrait;
import software.amazon.smithy.model.traits.OutputTrait;

import java.util.logging.Logger;

public class DirectedGoCodegen implements DirectedCodegen<GenerationContext, GoSettings, GoIntegration> {
    private static final Logger LOGGER = Logger.getLogger(DirectedGoCodegen.class.getName());
    @Override
    public SymbolProvider createSymbolProvider(CreateSymbolProviderDirective<GoSettings> directive) {
        return new SymbolVisitor(directive.model(), directive.settings());
    }

    @Override
    public GenerationContext createContext(CreateContextDirective<GoSettings, GoIntegration> directive) {
        return GenerationContext.builder()
                                .model(directive.model())
                                .settings(directive.settings())
                                .symbolProvider(directive.symbolProvider())
                                .fileManifest(directive.fileManifest())
                                .integrations(directive.integrations())
                                .writerDelegator(new GoDelegator(directive.fileManifest(), directive.symbolProvider()))
                                .protocolGenerator(new DafnyTypeConversionProtocol())
                                .build();
    }

    @Override
    public void generateService(GenerateServiceDirective<GenerationContext, GoSettings> directive) {
        new ClientGenerator(directive.context(), directive.service()).run();

        var protocolGenerator = directive.context().protocolGenerator();
        if (protocolGenerator == null) {
            return;
        }

        protocolGenerator.generateSharedSerializerComponents(directive.context());
        protocolGenerator.generateRequestSerializers(directive.context());

        protocolGenerator.generateSharedDeserializerComponents(directive.context());
        protocolGenerator.generateResponseDeserializers(directive.context());

        protocolGenerator.generateProtocolTests(directive.context());
    }

    @Override
    public void generateStructure(GenerateStructureDirective<GenerationContext, GoSettings> directive) {
        directive.context().writerDelegator().useShapeWriter(directive.shape(), writer -> {
            StructureGenerator generator = new StructureGenerator(
                    directive.model(),
                    directive.symbolProvider(),
                    writer,
                    directive.shape()
            );
            generator.run();
        });
    }

    @Override
    public void generateError(GenerateErrorDirective<GenerationContext, GoSettings> directive) {
        directive.context().writerDelegator().useShapeWriter(directive.shape(), writer -> {
            StructureGenerator generator = new StructureGenerator(
                    directive.model(),
                    directive.symbolProvider(),
                    writer,
                    directive.shape()
            );
            generator.run();
        });
    }

    @Override
    public void generateUnion(GenerateUnionDirective<GenerationContext, GoSettings> directive) {

    }

    @Override
    public void generateEnumShape(GenerateEnumDirective<GenerationContext, GoSettings> directive) {

    }

    @Override
    public void generateIntEnumShape(GenerateIntEnumDirective<GenerationContext, GoSettings> directive) {

    }
}
