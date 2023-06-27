package software.amazon.polymorph.smithygo;

import software.amazon.polymorph.smithygo.integration.GoIntegration;
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
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.traits.InputTrait;
import software.amazon.smithy.model.traits.OutputTrait;

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
        GoDelegator writerDelegator = directive.context().writerDelegator();
        Model model = directive.model();
        SymbolProvider symbolProvider = directive.symbolProvider();
        new LocalServiceGenerator(writerDelegator, model, symbolProvider).generate(directive.service());
    }

    @Override
    public void generateStructure(GenerateStructureDirective<GoCodegenContext, GoSettings> directive) {
        GoDelegator writerDelegator = directive.context().writerDelegator();
        Model model = directive.model();
        SymbolProvider symbolProvider = directive.symbolProvider();
        StructureGenerator structureGenerator = new StructureGenerator(model, symbolProvider, writerDelegator);
        structureGenerator.generate(directive.shape());
    }

    @Override
    public void generateError(GenerateErrorDirective<GoCodegenContext, GoSettings> directive) {
        GoDelegator writerDelegator = directive.context().writerDelegator();
        Model model = directive.model();
        SymbolProvider symbolProvider = directive.symbolProvider();
        StructureGenerator structureGenerator = new StructureGenerator(model, symbolProvider, writerDelegator);
        if(directive.shape().hasTrait(InputTrait.class) || directive.shape().hasTrait(OutputTrait.class)) {
            return;
        }
        structureGenerator.generate(directive.shape());
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
