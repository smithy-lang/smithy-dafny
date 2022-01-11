// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph;

import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.shapes.SmithyIdlModelSerializer;
import software.amazon.smithy.model.traits.DocumentationTrait;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Arrays;
import java.util.Collections;
import java.util.Map;
import java.util.Objects;
import java.util.logging.Logger;
import java.util.stream.Stream;

public class SmithyModelToIdl {
    private static final Path PACKAGE_MODEL_RESOURCES_PATH = Path.of("src", "main", "resources", "META-INF", "smithy");

    public static void main(String[] args) {
        final Logger logger = Logger.getLogger(SmithyModelToIdl.class.getSimpleName());

        if (args.length < 3) {
            throw new IllegalStateException("usage: SmithyModelToIdl DEST_PATH SMITHY_REPO_PATH MODEL_PATH...");
        }

        final Path destPath = Path.of(args[0]);
        final Path smithyRepoPath = Path.of(args[1]);

        final ModelAssembler modelAssembler = new ModelAssembler();

        for (int i = 2; i < args.length; i++) {
            final Path modelPath = Path.of(args[i]);
            modelAssembler.addImport(modelPath);
        }

        final File[] smithyRepoPackages = smithyRepoPath.toFile().listFiles();
        if (smithyRepoPackages == null) {
            throw new IllegalStateException("no Smithy repo packages found");
        }
        Arrays.stream(smithyRepoPackages)
                .map(pkg -> pkg.toPath().resolve(PACKAGE_MODEL_RESOURCES_PATH).toFile())
                .map(dir -> dir.listFiles((_dir, name) -> name.endsWith(".smithy") || name.endsWith(".json")))
                .filter(Objects::nonNull)
                .flatMap(Stream::of)
                .map(File::toPath)
                .forEach(modelAssembler::addImport);

        final Model model = modelAssembler.assemble().unwrap();

        final var serializer = SmithyIdlModelSerializer.builder()
                .basePath(destPath)
                // Omit documentation since it's visually distracting
                .traitFilter(trait -> !(trait instanceof DocumentationTrait))
                .build();
        final Map<Path, String> serializedFiles = serializer.serialize(model);
        serializedFiles.forEach((path, code) -> {
            try {
                Files.write(path, Collections.singleton(code));
                logger.info("Wrote " + path.toAbsolutePath());
            } catch (IOException e) {
                e.printStackTrace();
            }
        });
    }
}
