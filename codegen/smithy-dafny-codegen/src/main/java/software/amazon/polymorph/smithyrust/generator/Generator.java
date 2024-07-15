package software.amazon.polymorph.smithyrust.generator;

import software.amazon.polymorph.utils.IOUtils;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.build.FileManifest;
import software.amazon.smithy.build.PluginContext;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.node.ArrayNode;
import software.amazon.smithy.model.node.ObjectNode;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.rust.codegen.client.smithy.ClientCodegenVisitor;
import software.amazon.smithy.rust.codegen.client.smithy.customizations.ClientCustomizations;
import software.amazon.smithy.rust.codegen.client.smithy.customizations.HttpAuthDecorator;
import software.amazon.smithy.rust.codegen.client.smithy.customizations.HttpConnectorConfigDecorator;
import software.amazon.smithy.rust.codegen.client.smithy.customizations.IdempotencyTokenDecorator;
import software.amazon.smithy.rust.codegen.client.smithy.customizations.NoAuthDecorator;
import software.amazon.smithy.rust.codegen.client.smithy.customizations.SensitiveOutputDecorator;
import software.amazon.smithy.rust.codegen.client.smithy.customize.ClientCodegenDecorator;
import software.amazon.smithy.rust.codegen.client.smithy.customize.CombinedClientCodegenDecorator;
import software.amazon.smithy.rust.codegen.client.smithy.customize.RequiredCustomizations;
import software.amazon.smithy.rust.codegen.client.smithy.endpoint.EndpointParamsDecorator;
import software.amazon.smithy.rust.codegen.client.smithy.endpoint.EndpointsDecorator;
import software.amazon.smithy.rust.codegen.client.smithy.generators.client.FluentClientDecorator;
import software.amazon.smithy.rust.codegen.client.smithy.generators.config.StalledStreamProtectionDecorator;

import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.logging.Logger;
import java.util.stream.Collectors;

import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toSnakeCase;

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
        final var rustFiles = rustFiles(model);
        final LinkedHashMap<Path, TokenTree> tokenTreeMap = new LinkedHashMap<>();
        for (RustFile rustFile : rustFiles) {
            tokenTreeMap.put(rustFile.path(), rustFile.content());
        }
        IOUtils.writeTokenTreesIntoDir(tokenTreeMap, outputDir);
    }

    private static Set<RustFile> rustFiles(final Model model) {
        ServiceShape service = model.getServiceShapes().stream().findFirst().get();

        return model.getOperationShapes().stream()
                .flatMap(operationShape -> operationShape.getErrors().stream())
                .distinct()
                .map(errorShapeId -> errorConversionModule(service, model.expectShape(errorShapeId)))
                .collect(Collectors.toSet());
    }

    private static RustFile errorConversionModule(final ServiceShape service, final Shape errorStructure) {
        String structureName = errorStructure.getId().getName();
        String snakeCaseName = toSnakeCase(structureName);
        Path path = Path.of("src", "conversions", "error", snakeCaseName + ".rs");
        String template = """
        // Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
        
        #[allow(dead_code)]
        pub fn to_dafny(
            value: $sdkCrate:L::types::error::$structureName:L,
        ) -> ::std::rc::Rc<crate::implementation_from_dafny::r#$dafnyTypesModuleName:L::Error>{
          ::std::rc::Rc::new(
            crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_d$sdkCrate:L_dinternaldafny_dtypes::Error::$structureName:L {
              message: dafny_standard_library::conversion::ostring_to_dafny(&value.message)
            }
          )
        }
        """;
        String sdkId = service.expectTrait(ServiceTrait.class).getSdkId().toLowerCase();
        String evaluated = IOUtils.evalTemplate(template, Map.of(
                "sdkCrate", "aws_sdk_" + sdkId,
                "structureName", structureName,
                "dafnyTypesModuleName", "_software_damazon_dcryptography_dservices_d%s_dinternaldafny_dtypes".formatted(sdkId)
        ));
        return new RustFile(path, TokenTree.of(evaluated));
    }
}
