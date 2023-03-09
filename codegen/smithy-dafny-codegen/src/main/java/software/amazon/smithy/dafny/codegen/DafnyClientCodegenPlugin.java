package software.amazon.smithy.dafny.codegen;

import software.amazon.smithy.build.PluginContext;
import software.amazon.smithy.build.SmithyBuildPlugin;

public final class DafnyClientCodegenPlugin implements SmithyBuildPlugin {
    @Override
    public String getName() {
        return "dafny-client-codegen";
    }

    @Override
    public void execute(PluginContext context) {
        // TODO generate code
    }
}
