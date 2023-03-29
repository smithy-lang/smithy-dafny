// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.smithy.dafny.codegen;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import software.amazon.polymorph.CodegenEngine;
import software.amazon.polymorph.CodegenEngine.TargetLanguage;
import software.amazon.smithy.build.PluginContext;
import software.amazon.smithy.build.SmithyBuildPlugin;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.node.ObjectNode;
import software.amazon.smithy.model.node.StringNode;
import software.amazon.smithy.model.shapes.ShapeId;

import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public final class DafnyClientCodegenPlugin implements SmithyBuildPlugin {
    private static final Logger LOGGER = LoggerFactory.getLogger(DafnyClientCodegenPlugin.class);

    @Override
    public String getName() {
        return "dafny-client-codegen";
    }

    @Override
    public void execute(PluginContext context) {
        final Model model = context.getModel();
        final Settings settings = Settings.fromObject(context.getSettings())
                .orElseThrow(() -> new RuntimeException("Invalid plugin settings; aborting"));

        final Map<TargetLanguage, Path> outputDirs = new HashMap<>();
        settings.targetLanguages.forEach(lang -> {
            final Path dir;
            if (lang == TargetLanguage.DAFNY) {
                dir = Paths.get("Model");
            } else {
                dir = Paths.get("runtimes", lang.name().toLowerCase(), "Generated");
            }
            outputDirs.put(lang, context.getFileManifest().resolvePath(dir));
        });

        // TODO generate Makefile

        final CodegenEngine codegenEngine = new CodegenEngine.Builder()
                .withServiceModel(model)
                .withNamespace(settings.serviceId.getNamespace())
                .withTargetLangOutputDirs(outputDirs)
                .withAwsSdkStyle(true)  // TODO allow generating library-style code
                .build();
        codegenEngine.run();
    }

    static class Settings {
        public final ShapeId serviceId;
        public final Set<TargetLanguage> targetLanguages;
        public final Path includeDafnyFile;

        private Settings(final ShapeId serviceId, final Set<TargetLanguage> targetLanguages, final Path includeDafnyFile) {
            this.serviceId = serviceId;
            this.targetLanguages = targetLanguages;
            this.includeDafnyFile = includeDafnyFile;
        }

        static Optional<Settings> fromObject(final ObjectNode node) {
            final ShapeId serviceId = node.expectStringMember("serviceId").expectShapeId();

            final List<StringNode> targetLangNodes = node.expectArrayMember("targetLanguages").getElementsAs(StringNode.class);
            AtomicBoolean foundUnknownTargetLanguage = new AtomicBoolean(false);
            final Set<TargetLanguage> targetLanguages = targetLangNodes.stream()
                    .flatMap(strNode -> switch (strNode.getValue().toUpperCase()) {
                        case "JAVA" -> Stream.of(TargetLanguage.JAVA);
                        case "DOTNET", "CSHARP", "CS" -> Stream.of(TargetLanguage.DOTNET);
                        default -> {
                            LOGGER.error("Unknown target language: {}", strNode.getValue());
                            foundUnknownTargetLanguage.set(true);
                            yield Stream.empty();
                        }
                    }).collect(Collectors.toSet());
            if (foundUnknownTargetLanguage.get()) {
                return Optional.empty();
            }
            if (targetLanguages.size() < targetLangNodes.size()) {
                LOGGER.error("Duplicate target languages specified; aborting");
                return Optional.empty();
            }

            final String includeDafnyFileStr = node.expectStringMember("includeDafnyFile").getValue();
            final Path includeDafnyFile = Paths.get(includeDafnyFileStr).toAbsolutePath().normalize();
            if (Files.notExists(includeDafnyFile)) {
                LOGGER.warn("includeDafnyFile not found; generated Dafny code may not compile!");
            }

            return Optional.of(new Settings(serviceId, targetLanguages, includeDafnyFile));
        }
    }
}
