package software.amazon.polymorph.smithygo.codegen;

import software.amazon.polymorph.smithygo.codegen.integration.GoIntegration;
import software.amazon.smithy.build.PluginContext;
import software.amazon.smithy.build.SmithyBuildPlugin;
import software.amazon.smithy.codegen.core.directed.CodegenDirector;

public class GoClientCodegenPlugin implements SmithyBuildPlugin {
    public void run(PluginContext context) {
        CodegenDirector<GoWriter, GoIntegration, GenerationContext, GoSettings> runner
                = new CodegenDirector<>();

        runner.directedCodegen(new DirectedGoCodegen());

        // Set the SmithyIntegration class to look for and apply using SPI.
        runner.integrationClass(GoIntegration.class);

        // Set the FileManifest and Model from the plugin.
        runner.fileManifest(context.getFileManifest());
        runner.model(context.getModel());

        // Create the GoSettings object from the plugin settings.
        GoSettings settings = GoSettings.from(context.getSettings());
        runner.settings(settings);

        runner.service(settings.getService());

        // Configure the director to perform some common model transforms.
        runner.performDefaultCodegenTransforms();

        // TODO: Not using below because it would break existing AWS SDKs. Maybe it should be configurable
        // so generic SDKs call this by default, but AWS SDKs can opt-out of it via a setting.
        // runner.createDedicatedInputsAndOutputs();

        // Run it!
        runner.run();
    }

    @Override
    public String getName() {
        return "go-client-codegen";
    }

    @Override
    public void execute(PluginContext context) {
        this.run(context);
    }
}
