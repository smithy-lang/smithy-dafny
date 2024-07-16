package software.amazon.polymorph.smithyrust.generator;

import software.amazon.polymorph.utils.IOUtils;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.build.FileManifest;
import software.amazon.smithy.build.PluginContext;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.node.ArrayNode;
import software.amazon.smithy.model.node.ObjectNode;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.EnumDefinition;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.RequiredTrait;
import software.amazon.smithy.model.traits.Trait;
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
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;
import java.util.logging.Logger;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static software.amazon.polymorph.utils.IOUtils.evalTemplate;
import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toPascalCase;
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

    private static Stream<StructureShape> allErrorShapes(final Model model, final ServiceShape service) {
        return model.getOperationShapes().stream()
                .flatMap(operationShape -> operationShape.getErrors().stream())
                .distinct()
                .map(errorShapeId -> model.expectShape(errorShapeId, StructureShape.class));
    }

    private static Set<RustFile> rustFiles(final Model model) {
        ServiceShape service = model.getServiceShapes().stream().findFirst().get();

        Set<RustFile> result = new HashSet<>();
        result.addAll(allErrorShapes(model, service)
                .map(errorShape -> errorConversionModule(service, errorShape))
                .collect(Collectors.toSet()));

        result.addAll(model.getStringShapesWithTrait(EnumTrait.class).stream()
                .map(enumShape -> enumConversionModule(service, enumShape))
                .collect(Collectors.toSet()));

        result.add(conversionsModuleFile(model, service));
        result.addAll(allOperationConversionModules(model, service));
        result.add(conversionsErrorModule(model, service));

        result.add(libFile(service));

        return result;
    }

    private static Set<RustFile> allOperationConversionModules(final Model model, final ServiceShape service) {
        return service.getOperations().stream()
                .map(shapeId -> operationConversionModules(model, service, model.expectShape(shapeId, OperationShape.class)))
                .flatMap(s -> s.stream())
                .collect(Collectors.toSet());
    }

    private static Set<RustFile> operationConversionModules(final Model model, final ServiceShape service, final OperationShape operationShape) {
        var operationModuleName = toSnakeCase(operationShape.getId().getName());
        var operationModuleContent = declarePubModules(Stream.of(
                "_" + operationModuleName + "_request",
                "_" + operationModuleName + "_response"
        ));
        RustFile outerModule = new RustFile(Path.of("src", "conversions", operationModuleName + ".rs"), operationModuleContent);

        RustFile requestModule = operationRequestConversionModule(model, service, operationShape);

        return Set.of(outerModule, requestModule);
    }

    private static RustFile operationRequestConversionModule(final Model model, final ServiceShape service, final OperationShape operationShape) {
        var operationModuleName = toSnakeCase(operationShape.getId().getName());

        var toDafnyFunction = operationRequestToDafnyFunction(model, service, operationShape);

        return new RustFile(Path.of("src", "conversions", operationModuleName, "_" + operationModuleName + "_request.rs"), toDafnyFunction);
    }

    private static TokenTree operationRequestToDafnyFunction(final Model model, final ServiceShape service, final OperationShape operationShape) {
        StructureShape inputShape = model.expectShape(operationShape.getInputShape(), StructureShape.class);
        String operationName = operationShape.getId().getName();
        String snakeCaseOperationName = toSnakeCase(operationName);
        String sdkId = service.expectTrait(ServiceTrait.class).getSdkId().toLowerCase();
        String dafnyTypesModuleName = "_software_damazon_dcryptography_dservices_d%s_dinternaldafny_dtypes".formatted(sdkId);
        String structureName = inputShape.getId().getName();
        Map<String, String> variables = Map.of(
                "sdkCrate", "aws_sdk_" + sdkId,
                "operationName", operationName,
                "structureName", structureName,
                "snakeCaseOperationName", snakeCaseOperationName,
                "dafnyTypesModuleName", dafnyTypesModuleName
        );

        String sdkTypeName = evalTemplate("$sdkCrate:L::types::$enumName:L", variables);

        var prelude = TokenTree.of(evalTemplate("""
        #[allow(dead_code)]
        pub fn to_dafny(
            value: $sdkCrate:L::operation::$snakeCaseOperationName:L::$structureName:L
        ) -> ::std::rc::Rc<
            crate::implementation_from_dafny::r#$dafnyTypesModuleName:L::$structureName:L,
        >{
            ::std::rc::Rc::new(crate::implementation_from_dafny::r#$dafnyTypesModuleName:L::$structureName:L::$structureName:L {

        """, variables));

        var variants = TokenTree.of(inputShape.members()
                .stream()
                .map(m -> TokenTree.of(m.getMemberName()
                        + ": "
                        + variantMemberForOperationRequest(model, m) + ","))
        ).lineSeparated();
        final var postlude = TokenTree.of("""
            })
        }
        """);

        return TokenTree.of(prelude, variants, postlude);
    }

    private static TokenTree variantMemberForOperationRequest(final Model model, final MemberShape member) {
        Shape targetShape = model.expectShape(member.getTarget());
        String snakeCaseMemberName = toSnakeCase(member.getMemberName());
        return switch (targetShape.getType()) {
            case STRING -> {
                if (targetShape.hasTrait(EnumTrait.class)) {
                    yield TokenTree.of("""
                    ::std::rc::Rc::new(match value.%s {
                        Some(x) => crate::implementation_from_dafny::_Wrappers_Compile::Option::Some { value: crate::conversions::%s::to_dafny(x) },
                        None => crate::implementation_from_dafny::_Wrappers_Compile::Option::None { }
                    })
                    """.formatted(snakeCaseMemberName, snakeCaseMemberName));
                } else {
                    if (member.hasTrait(RequiredTrait.class)) {
                        yield TokenTree.of("dafny_standard_library::conversion::ostring_to_dafny(&value.%s).Extract()".formatted(snakeCaseMemberName));
                    } else {
                        yield TokenTree.of("dafny_standard_library::conversion::ostring_to_dafny(&value.%s)".formatted(snakeCaseMemberName));
                    }
                }
            }
            default -> TokenTree.of("todo!()");
        };
    }

    private static RustFile libFile(final ServiceShape service) {
        return new RustFile(Path.of("src", "lib.rs"),
                TokenTree.of("""
                        mod client;
                        mod conversions;
                        pub mod implementation_from_dafny;
                        """));
    }

//    private static RustFile clientModuleFile(final ServiceShape service) {
//        Set<>
//    }

    private static RustFile conversionsErrorModule(final Model model, final ServiceShape service) {
        TokenTree content = declarePubModules(allErrorShapes(model, service)
                .map(structureShape -> toSnakeCase(structureShape.getId().getName())));
        return new RustFile(Path.of("src", "conversions", "error.rs"), content);
    }

    private static RustFile conversionsModuleFile(final Model model, final ServiceShape service) {
        Stream<String> operationModules = model.getOperationShapes()
                .stream()
                .map(operationShape -> toSnakeCase(operationShape.getId().getName()));

        Stream<String> structureModules = model.getStructureShapes()
                .stream()
                .filter(structureShape -> !structureShape.hasTrait(ErrorTrait.class) && !structureShape.hasTrait(Trait.class))
                .map(structureShape -> toSnakeCase(structureShape.getId().getName()));

        Stream<String> enumModules = model.getStringShapesWithTrait(EnumTrait.class).stream()
                .map(structureShape -> toSnakeCase(structureShape.getId().getName()));

        TokenTree content = declarePubModules(
                Stream.of(operationModules, structureModules, enumModules, Stream.of("error"))
                        .flatMap(s -> s));

        return new RustFile(Path.of("src", "conversions.rs"), content);

    }

    private static TokenTree declarePubModules(Stream<String> moduleNames) {
        return TokenTree.of(
            moduleNames.map(module -> TokenTree.of("pub mod " + module + ";\n")))
        .lineSeparated();
    }

    private static RustFile errorConversionModule(final ServiceShape service, final Shape errorStructure) {
        String structureName = errorStructure.getId().getName();
        String snakeCaseName = toSnakeCase(structureName);
        Path path = Path.of("src", "conversions", "error", snakeCaseName + ".rs");
        String template = """
        // Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
        
        #[allow(dead_code)]
        pub fn to_dafny(
            value: aws_sdk_$sdkId:L::types::error::$structureName:L,
        ) -> ::std::rc::Rc<crate::implementation_from_dafny::r#$dafnyTypesModuleName:L::Error>{
          ::std::rc::Rc::new(
            crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_d$sdkId:L_dinternaldafny_dtypes::Error::$structureName:L {
              message: dafny_standard_library::conversion::ostring_to_dafny(&value.message)
            }
          )
        }
        """;
        String sdkId = service.expectTrait(ServiceTrait.class).getSdkId().toLowerCase();
        String evaluated = evalTemplate(template, Map.of(
                "sdkId", sdkId,
                "structureName", structureName,
                "dafnyTypesModuleName", "_software_damazon_dcryptography_dservices_d%s_dinternaldafny_dtypes".formatted(sdkId)
        ));
        return new RustFile(path, TokenTree.of(evaluated));
    }

    private static RustFile enumConversionModule(final ServiceShape service, final Shape enumShape) {
        String enumName = enumShape.getId().getName();
        String snakeCaseName = toSnakeCase(enumName);
        String sdkId = service.expectTrait(ServiceTrait.class).getSdkId().toLowerCase();
        String dafnyTypesModuleName = "_software_damazon_dcryptography_dservices_d%s_dinternaldafny_dtypes".formatted(sdkId);
        Map<String, String> variables = Map.of(
                "sdkCrate", "aws_sdk_" + sdkId,
                "enumName", enumName,
                "dafnyTypesModuleName", dafnyTypesModuleName
        );

        Path path = Path.of("src", "conversions", snakeCaseName + ".rs");
        String sdkTypeName = evalTemplate("$sdkCrate:L::types::$enumName:L", variables);

        var prelude = TokenTree.of(evalTemplate("""
        // Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
        #[allow(dead_code)]
         
        pub fn to_dafny(
            value: $sdkCrate:L::types::$enumName:L,
        ) -> ::std::rc::Rc<crate::implementation_from_dafny::r#$dafnyTypesModuleName:L::$enumName:L>{
            ::std::rc::Rc::new(match value {

        """, variables));

        var branches = TokenTree.of(enumShape.expectTrait(EnumTrait.class).getValues()
                .stream()
                .map(e -> TokenTree.of(sdkTypeName
                        + "::"
                        + rustEnumName(e)
                        + " => crate::implementation_from_dafny::r#"
                        + dafnyTypesModuleName
                        + "::"
                        + enumName
                        + "::"
                        + dafnyEnumName(e)
                        + " {},"))
        ).lineSeparated();
        final var postlude = TokenTree.of("""

                // TODO: This should not be a panic, but the Dafny image of the enum shape doesn't have an Unknown variant of any kind,
                // so there's no way to succeed.
                // See https://github.com/smithy-lang/smithy-dafny/issues/476.
                // This could be handled more cleanly if conversion functions returned Results,
                // but that would be a large and disruptive change to the overall code flow.
                _ => panic!("Unknown enum variant: {}", value),
            })
        }
        """);

        return new RustFile(path, TokenTree.of(prelude, branches, postlude));
    }

    private static String rustEnumName(EnumDefinition ed) {
        return toPascalCase(ed.getValue());
    }

    private static String dafnyEnumName(EnumDefinition ed) {
        return ed.getValue();
    }
}
