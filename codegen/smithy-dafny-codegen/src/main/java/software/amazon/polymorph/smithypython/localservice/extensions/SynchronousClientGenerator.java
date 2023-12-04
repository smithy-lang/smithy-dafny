package software.amazon.polymorph.smithypython.localservice.extensions;

import java.util.LinkedHashSet;

import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolReference;
import software.amazon.smithy.model.knowledge.TopDownIndex;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.traits.DocumentationTrait;
import software.amazon.smithy.model.traits.StringTrait;
import software.amazon.smithy.python.codegen.ClientGenerator;
import software.amazon.smithy.python.codegen.CodegenUtils;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.integration.PythonIntegration;
import software.amazon.smithy.python.codegen.integration.RuntimeClientPlugin;

public class SynchronousClientGenerator extends ClientGenerator {

    SynchronousClientGenerator(GenerationContext context, ServiceShape service) {
        super(context, service);
        //TODO Auto-generated constructor stub
    }

    @Override
    protected void generateService(PythonWriter writer) {
        var serviceSymbol = context.symbolProvider().toSymbol(service);
        var pluginSymbol = CodegenUtils.getPluginSymbol(context.settings());
        
        var configShapeId = service.getTrait(LocalServiceTrait.class).get().getConfigId();
        // TODO-Python: Create a new SymbolVisitor... Smithy-Python is dumb about 
        // knowing where classes are actually generated, and tries to import
        // the config from .models
        // var configSymbol = context.symbolProvider().toSymbol(
        //     context.model().expectShape(configShapeId)
        // );
        writer.addImport(".config", configShapeId.getName());
        
        writer.addStdlibImport("typing", "TypeVar");
        writer.write("""
            Input = TypeVar("Input")
            Output = TypeVar("Output")
            """);

        writer.openBlock("class $L:", "", serviceSymbol.getName(), () -> {
            var docs = service.getTrait(DocumentationTrait.class)
                    .map(StringTrait::getValue)
                    .orElse("Client for " + serviceSymbol.getName());
            writer.writeDocs(() -> {
                writer.write("""
                        $L

                        :param config: Configuration for the client.""", docs);
            });

            var defaultPlugins = new LinkedHashSet<SymbolReference>();

            for (PythonIntegration integration : context.integrations()) {
                for (RuntimeClientPlugin runtimeClientPlugin : integration.getClientPlugins()) {
                    if (runtimeClientPlugin.matchesService(context.model(), service)) {
                        runtimeClientPlugin.getPythonPlugin().ifPresent(defaultPlugins::add);
                    }
                }
            }

            writer.write("""
                    def __init__(
                        self,
                        config: $1L | None = None
                    ):
                        self._config = config or $1L()

                        client_plugins: list[$2T] = [
                            $3C
                        ]

                        for plugin in client_plugins:
                            plugin(self._config)
                    """, configShapeId.getName(), pluginSymbol, writer.consumer(w -> writeDefaultPlugins(w, defaultPlugins)));

            writer.addStdlibImport(
                DafnyNameResolver.getDafnyTypesModuleNameForSmithyNamespace(service.getId().getNamespace()),
                DafnyNameResolver.getDafnyClientInterfaceTypeForServiceShape(service)
            );

            writer.write("""
                    def __init__(
                        self,
                        config: $1L | None = None,
                        dafny_client: $2L | None = None
                    ):
                        if config is None:
                            self._config = Config()
                        else:
                            self.__init__(config)
                        
                        if dafny_client is not None:
                            self._config.dafnyImplInterface._impl = dafny_client

                    """, configShapeId.getName(), DafnyNameResolver.getDafnyClientInterfaceTypeForServiceShape(service));

            var topDownIndex = TopDownIndex.of(context.model());
            for (OperationShape operation : topDownIndex.getContainedOperations(service)) {
                generateOperation(writer, operation);
            }
        });

        if (context.protocolGenerator() != null) {
            generateOperationExecutor(writer);
        }
    }

    @Override
    protected void generateOperation(PythonWriter writer, OperationShape operation) {
        var operationSymbol = context.symbolProvider().toSymbol(operation);

        var input = context.model().expectShape(operation.getInputShape());
        var inputSymbol = context.symbolProvider().toSymbol(input);

        var output = context.model().expectShape(operation.getOutputShape());
        var outputSymbol = context.symbolProvider().toSymbol(output);

        writer.openBlock("def $L(self, input: $T) -> $T:", "",
                operationSymbol.getName(), inputSymbol, outputSymbol, () -> {
            writer.writeDocs(() -> {
                // TODO: Point to Polymorph Javadoc trait
                var docs = operation.getTrait(DocumentationTrait.class)
                        .map(StringTrait::getValue)
                        .orElse(String.format("Invokes the %s operation.", operation.getId().getName()));

                var inputDocs = input.getTrait(DocumentationTrait.class)
                        .map(StringTrait::getValue)
                        .orElse("The operation's input.");

                writer.write("""
                        $L

                        :param input: $L""", docs, inputDocs);
            });

            if (context.protocolGenerator() == null) {
                writer.write("raise NotImplementedError()");
            } else {
                var protocolGenerator = context.protocolGenerator();
                var serSymbol = protocolGenerator.getSerializationFunction(context, operation);
                var deserSymbol = protocolGenerator.getDeserializationFunction(context, operation);
                writer.addStdlibImport("asyncio");
                writer.write("""
                    return asyncio.run(self._execute_operation(
                        input=input,
                        plugins=[],
                        serialize=$T,
                        deserialize=$T,
                        config=self._config,
                        operation_name=$S,
                    ))
                    """, serSymbol, deserSymbol, operation.getId().getName());
            }
        });
    }


    
}
