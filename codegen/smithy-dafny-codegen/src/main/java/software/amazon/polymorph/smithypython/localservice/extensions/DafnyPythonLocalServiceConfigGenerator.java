package software.amazon.polymorph.smithypython.localservice.extensions;

import static java.lang.String.format;

import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.model.knowledge.TopDownIndex;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.python.codegen.*;

/**
 * Override Smithy-Python's ConfigGenerator to support namespaces in other modules
 * via the getPythonModuleSmithygeneratedPathForSmithyNamespace method.
 */
public class DafnyPythonLocalServiceConfigGenerator extends ConfigGenerator {

  public DafnyPythonLocalServiceConfigGenerator(
    PythonSettings settings,
    GenerationContext context
  ) {
    super(settings, context);
  }

  @Override
  public void run() {
    var config = Symbol
      .builder()
      .name("Config")
      .namespace(
        format(
          "%s.config",
          SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
            settings.getService().getNamespace(),
            context
          )
        ),
        "."
      )
      .definitionFile(
        format(
          "./%s/config.py",
          SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
            settings.getService().getNamespace()
          )
        )
      )
      .build();
    context
      .writerDelegator()
      .useFileWriter(
        config.getDefinitionFile(),
        config.getNamespace(),
        writer -> {
          writeInterceptorsType(writer);
          generateConfig(context, writer);
        }
      );

    var plugin = Symbol
      .builder()
      .name("Plugin")
      .namespace(
        format(
          "%s.config",
          SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
            settings.getService().getNamespace(),
            context
          )
        ),
        "."
      )
      .definitionFile(
        format(
          "./%s/config.py",
          SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
            settings.getService().getNamespace()
          )
        )
      )
      .build();
    context
      .writerDelegator()
      .useFileWriter(
        plugin.getDefinitionFile(),
        plugin.getNamespace(),
        writer -> {
          writer.addStdlibImport("typing", "Callable");
          writer.addStdlibImport("typing", "TypeAlias");
          writer.writeComment(
            "A callable that allows customizing the config object on each request."
          );
          writer.write(
            "$L: TypeAlias = Callable[[$T], None]",
            plugin.getName(),
            config
          );
        }
      );
  }

  // Write `Any`. Typehints here introduce a circular dependency in case of reference shapes.
  protected void writeInterceptorsType(PythonWriter writer) {
    writer.addStdlibImport("typing", "Any");
    writer.write("_ServiceInterceptor = Any");
  }
}
