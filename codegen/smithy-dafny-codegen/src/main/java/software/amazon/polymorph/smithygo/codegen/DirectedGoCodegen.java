package software.amazon.polymorph.smithygo.codegen;

import software.amazon.polymorph.smithygo.DafnyTypeConversionProtocol;
import software.amazon.polymorph.smithygo.codegen.integration.GoIntegration;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.codegen.core.directed.CreateContextDirective;
import software.amazon.smithy.codegen.core.directed.CreateSymbolProviderDirective;
import software.amazon.smithy.codegen.core.directed.DirectedCodegen;
import software.amazon.smithy.codegen.core.directed.GenerateEnumDirective;
import software.amazon.smithy.codegen.core.directed.GenerateErrorDirective;
import software.amazon.smithy.codegen.core.directed.GenerateIntEnumDirective;
import software.amazon.smithy.codegen.core.directed.GenerateResourceDirective;
import software.amazon.smithy.codegen.core.directed.GenerateServiceDirective;
import software.amazon.smithy.codegen.core.directed.GenerateStructureDirective;
import software.amazon.smithy.codegen.core.directed.GenerateUnionDirective;

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

        protocolGenerator.generateSerializers(directive.context());

        protocolGenerator.generateDeserializers(directive.context());

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
        directive.context().writerDelegator().useShapeWriter(directive.shape(), writer -> {
            EnumGenerator enumGenerator = new EnumGenerator(directive.symbolProvider(), writer, directive.shape());
            enumGenerator.run();
        });
    }

    @Override
    public void generateIntEnumShape(GenerateIntEnumDirective<GenerationContext, GoSettings> directive) {
        directive.context().writerDelegator().useShapeWriter(directive.shape(), writer -> {
            IntEnumGenerator intEnumGenerator = new IntEnumGenerator(directive.symbolProvider(), writer, directive.shape().asIntEnumShape().get());
            intEnumGenerator.run();
        });
    }

    @Override
    public void generateResource(GenerateResourceDirective<GenerationContext, GoSettings> directive) {
//        System.out.println("##############" + directive.shape());
//        directive.context().writerDelegator().useShapeWriter(directive.shape(), writer -> {
//        });
    }
}
