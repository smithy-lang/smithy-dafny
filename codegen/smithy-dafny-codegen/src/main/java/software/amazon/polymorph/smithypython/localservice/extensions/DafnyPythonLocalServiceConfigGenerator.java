package software.amazon.polymorph.smithypython.localservice.extensions;

import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.model.knowledge.TopDownIndex;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.python.codegen.*;

import static java.lang.String.format;

public class DafnyPythonLocalServiceConfigGenerator extends ConfigGenerator {

    public DafnyPythonLocalServiceConfigGenerator(PythonSettings settings, GenerationContext context) {
        super(settings, context);
    }

    @Override
    public void run() {
        var config = Symbol.builder()
                .name("Config")
                .namespace(format("%s.config", SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(settings.getService().getNamespace(), context)), ".")
                .definitionFile(format("./%s/config.py",  SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(settings.getService().getNamespace())))
                .build();
//        var config = CodegenUtils.getConfigSymbol(context.settings());
        context.writerDelegator().useFileWriter
                (config.getDefinitionFile(), config.getNamespace(), writer -> {
            writeInterceptorsType(writer);
            generateConfig(context, writer);
        });

        // Generate the plugin symbol. This is just a callable. We could do something
        // like have a class to implement, but that seems unnecessarily burdensome for
        // a single function.
        var plugin = Symbol.builder()
                .name("Plugin")
                .namespace(format("%s.config", SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(settings.getService().getNamespace(), context)), ".")
                .definitionFile(format("./%s/config.py",  SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(settings.getService().getNamespace())))
                .build();
        context.writerDelegator().useFileWriter(plugin.getDefinitionFile(), plugin.getNamespace(), writer -> {
            writer.addStdlibImport("typing", "Callable");
            writer.addStdlibImport("typing", "TypeAlias");
            writer.writeComment("A callable that allows customizing the config object on each request.");
            writer.write("$L: TypeAlias = Callable[[$T], None]", plugin.getName(), config);
        });
    }

    protected void writeInterceptorsType(PythonWriter writer) {
        var symbolProvider = context.symbolProvider();
        var operationShapes = TopDownIndex.of(context.model())
                .getContainedOperations(settings.getService());

        writer.addStdlibImport("typing", "Union");
        writer.addDependency(SmithyPythonDependency.SMITHY_PYTHON);
        writer.addImport("smithy_python.interfaces.interceptor", "Interceptor", "Interceptor");

        writer.writeInline("_ServiceInterceptor = Union[");
        if (operationShapes.isEmpty()) {
            writer.writeInline("None]");
        } else {
            var iter = operationShapes.iterator();
            while (iter.hasNext()) {
                var operation = iter.next();

                var operationInputShape = context.model().expectShape(operation.getInputShape()).asStructureShape().get();
                Symbol interceptorInputSymbol;
                if (operationInputShape.hasTrait(PositionalTrait.class)) {
                    final MemberShape onlyMember = PositionalTrait.onlyMember(operationInputShape);
                    final Shape targetShape = context.model().expectShape(onlyMember.getTarget());
                    interceptorInputSymbol = symbolProvider.toSymbol(targetShape);
                } else {
                    interceptorInputSymbol = symbolProvider.toSymbol(operationInputShape);
                }

                // TODO-Python: Handle positionals inside MY symbolProvider
                var operationOutputShape = context.model().expectShape(operation.getOutputShape()).asStructureShape().get();
                Symbol interceptorOutputSymbol;
                if (operationOutputShape.hasTrait(PositionalTrait.class)) {
                    final MemberShape onlyMember = PositionalTrait.onlyMember(operationOutputShape);
                    final Shape targetShape = context.model().expectShape(onlyMember.getTarget());
                    interceptorOutputSymbol = symbolProvider.toSymbol(targetShape);
                } else {
                    interceptorOutputSymbol = symbolProvider.toSymbol(operationOutputShape);
                }

                // TODO: pull the transport request/response types off of the application protocol
                writer.addStdlibImport("typing", "Any");
                writer.writeInline("Interceptor[$T, $T, Any, Any]", interceptorInputSymbol, interceptorOutputSymbol);
                if (iter.hasNext()) {
                    writer.writeInline(", ");
                } else {
                    writer.writeInline("]");
                }
            }
        }
        writer.write("");
    }

}
