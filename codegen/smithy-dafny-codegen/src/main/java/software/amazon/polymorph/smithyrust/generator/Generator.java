package software.amazon.polymorph.smithyrust.generator;

import software.amazon.smithy.build.FileManifest;
import software.amazon.smithy.build.PluginContext;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.node.ArrayNode;
import software.amazon.smithy.model.node.ObjectNode;
import software.amazon.smithy.rust.codegen.client.smithy.ClientCodegenVisitor;
import software.amazon.smithy.rust.codegen.client.smithy.customizations.ClientCustomizations;
import software.amazon.smithy.rust.codegen.client.smithy.customizations.HttpAuthDecorator;
import software.amazon.smithy.rust.codegen.client.smithy.customizations.HttpConnectorConfigDecorator;
import software.amazon.smithy.rust.codegen.client.smithy.customizations.IdempotencyTokenDecorator;
import software.amazon.smithy.rust.codegen.client.smithy.customizations.NoAuthDecorator;
import software.amazon.smithy.rust.codegen.client.smithy.customizations.SensitiveOutputDecorator;
import software.amazon.smithy.rust.codegen.client.smithy.endpoint.EndpointParamsDecorator;
import software.amazon.smithy.rust.codegen.client.smithy.endpoint.EndpointsDecorator;
import software.amazon.smithy.rust.codegen.client.smithy.generators.client.FluentClientDecorator;
import software.amazon.smithy.rust.codegen.client.smithy.generators.config.StalledStreamProtectionDecorator;
import software.amazon.smithy.rust.codegen.core.smithy.generators.*;
import software.amazon.smithy.rust.codegen.client.smithy.customize.*;

import java.nio.file.Path;
import java.util.logging.Logger;

public class Generator {

    public static void usingSmithyRs(final Model model, final Path outputDir) {
        // Mock up a PluginContext for the benefit of smithy-rs libraries
        FileManifest fileManifest = FileManifest.create(outputDir);
        ObjectNode settingsNode = ObjectNode.builder()
                .withMember("module", "SomeModule")
                .withMember("moduleVersion", "1")
                .withMember("moduleAuthors", ArrayNode.arrayNode())
                .build();
        PluginContext context = PluginContext.builder()
                .model(model)
                .fileManifest(fileManifest)
                .settings(settingsNode)
                .build();
        Logger logger = Logger.getLogger("TODO");

        ClientCodegenDecorator[] decorators = {
                new ClientCustomizations(),
                new RequiredCustomizations(),
                new FluentClientDecorator(),
                new EndpointsDecorator(),
                new EndpointParamsDecorator(),
                new NoAuthDecorator(),
                new HttpAuthDecorator(),
                new HttpConnectorConfigDecorator(),
                new SensitiveOutputDecorator(),
                new IdempotencyTokenDecorator(),
                new StalledStreamProtectionDecorator(),
                new LocalServiceDecorator()
        };
        CombinedClientCodegenDecorator codegenDecorator =
                CombinedClientCodegenDecorator.Companion.fromClasspath(
                        context, decorators, logger);

        // ClientCodegenVisitor is the main driver of code generation that traverses the model and generates code
        new ClientCodegenVisitor(context, codegenDecorator).execute();
    }

    public static void handRolled(final Model model, final Path outputDir) {
    }

}
