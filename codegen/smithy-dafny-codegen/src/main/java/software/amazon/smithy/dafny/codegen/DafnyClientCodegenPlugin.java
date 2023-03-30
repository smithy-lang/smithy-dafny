// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.smithy.dafny.codegen;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import software.amazon.polymorph.CodegenEngine;
import software.amazon.polymorph.CodegenEngine.TargetLanguage;
import software.amazon.smithy.build.FileManifest;
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
        final FileManifest manifest = context.getFileManifest();
        final Settings settings = Settings.fromObject(context.getSettings(), manifest)
                .orElseThrow(() -> new RuntimeException("Invalid plugin settings; aborting"));

        final Map<TargetLanguage, Path> outputDirs = new HashMap<>();
        outputDirs.put(TargetLanguage.DAFNY, manifest.resolvePath(Paths.get("Model")));
        settings.targetLanguages.forEach(lang -> {
            final Path dir = Paths.get("runtimes", lang.name().toLowerCase(), "Generated");
            outputDirs.put(lang, manifest.resolvePath(dir));
        });

        // TODO generate Makefile

        final CodegenEngine codegenEngine = new CodegenEngine.Builder()
                .withServiceModel(model)
                .withNamespace(settings.serviceId.getNamespace())
                .withTargetLangOutputDirs(outputDirs)
                .withAwsSdkStyle(true)  // this plugin only generated AWS SDK-style code
                .withIncludeDafnyFile(settings.includeDafnyFile)
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

        static Optional<Settings> fromObject(final ObjectNode node, final FileManifest manifest) {
            final ShapeId serviceId = node.expectStringMember("service").expectShapeId();

            final List<StringNode> targetLangNodes = node.expectArrayMember("targetLanguages").getElementsAs(StringNode.class);
            AtomicBoolean foundUnknownTargetLanguage = new AtomicBoolean(false);
            final Set<TargetLanguage> targetLanguages = targetLangNodes.stream()
                    .flatMap(strNode -> switch (strNode.getValue().toUpperCase()) {
                        case "JAVA" -> Stream.of(TargetLanguage.JAVA);
                        case "DOTNET", "CSHARP", "CS" -> Stream.of(TargetLanguage.DOTNET);
                        case "DAFNY" -> {
                            LOGGER.warn("Dafny code is always generated, and shouldn't be specified explicitly");
                            foundUnknownTargetLanguage.set(true);
                            yield Stream.empty();
                        }
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

            final Path buildRoot = findSmithyBuildJson(manifest.getBaseDir())
                    .orElseThrow(() -> new IllegalStateException("Couldn't find smithy-build.json"))
                    .getParent();
            final String includeDafnyFileStr = node.expectStringMember("includeDafnyFile").getValue();
            final Path includeDafnyFile = buildRoot.resolve(includeDafnyFileStr).toAbsolutePath().normalize();
            if (Files.notExists(includeDafnyFile)) {
                LOGGER.warn("Generated Dafny code may not compile because the includeDafnyFile could not be found: {}",
                        includeDafnyFile);
            }

            return Optional.of(new Settings(serviceId, targetLanguages, includeDafnyFile));
        }

        /**
         * Traverses up from the given start path,
         * searching for a "smithy-build.json" file and returning its path if found.
         */
        private static Optional<Path> findSmithyBuildJson(final Path start) {
            if (start == null || !start.isAbsolute()) {
                throw new IllegalArgumentException("Start path must be non-null and absolute");
            }
            Path cursor = start.normalize();
            final Path root = cursor.getRoot();
            // Shouldn't need to traverse more than 100 levels... but don't hang forever
            for (int i = 0; !root.equals(cursor) && i < 100; i++) {
                final Path config = cursor.resolve("smithy-build.json");
                if (Files.exists(config)) {
                    return Optional.of(config);
                }
                cursor = cursor.getParent();
            }
            return Optional.empty();
        }
    }
}
