// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.smithy.dafny.codegen;

import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.concurrent.atomic.AtomicBoolean;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import software.amazon.polymorph.CodegenEngine;
import software.amazon.polymorph.smithydafny.DafnyVersion;
import software.amazon.smithy.build.FileManifest;
import software.amazon.smithy.model.node.ObjectNode;
import software.amazon.smithy.model.node.StringNode;
import software.amazon.smithy.model.shapes.ShapeId;

class DafnyClientCodegenPluginSettings {

  private static final Logger LOGGER = LoggerFactory.getLogger(
    DafnyClientCodegenPluginSettings.class
  );

  /**
   * Configures the code generator to use the best practices of a specific edition.
   *
   * @see <a href="https://smithy.io/2.0/guides/building-codegen/configuring-the-generator.html#edition">
   *     Smithy <code>edition</code> property</a>
   */
  public final DafnyClientCodegenEdition edition;

  /**
   * The service shape ID for which to generate code.
   *
   * @see <a href="https://smithy.io/2.0/guides/building-codegen/configuring-the-generator.html#service">
   *     Smithy <code>service</code> property</a>
   */
  public final ShapeId serviceId;

  /**
   * Set of language(s) for which the plugin should generate code.
   * The plugin always generates Dafny code, so Dafny should not be specified explicitly.
   */
  public final Set<CodegenEngine.TargetLanguage> targetLanguages;

  /**
   * Path to the <code>TestModels/dafny-dependencies/StandardLibrary/src/Index.dfy</code> file in the smithy-dafny
   * repository, relative to the <code>smithy-build.json</code> file.
   * <p>
   * TODO: replace this with something cleaner
   */
  public final Path includeDafnyFile;

  /**
   * The Dafny version to generate code compatible with.
   * This is used to ensure both Dafny source compatibility
   * and compatibility with the Dafny compiler and runtime internals,
   * which shim code generation currently depends on.
   */
  public final DafnyVersion dafnyVersion;

  private DafnyClientCodegenPluginSettings(
    final DafnyClientCodegenEdition edition,
    final ShapeId serviceId,
    final Set<CodegenEngine.TargetLanguage> targetLanguages,
    final Path includeDafnyFile,
    final DafnyVersion dafnyVersion
  ) {
    this.edition = edition;
    this.serviceId = serviceId;
    this.targetLanguages = targetLanguages;
    this.includeDafnyFile = includeDafnyFile;
    this.dafnyVersion = dafnyVersion;
  }

  static Optional<DafnyClientCodegenPluginSettings> fromObject(
    final ObjectNode node,
    final FileManifest manifest
  ) {
    final ShapeId serviceId = node
      .expectStringMember("service")
      .expectShapeId();

    final String editionNumeric = node.expectStringMember("edition").getValue();
    final DafnyClientCodegenEdition edition =
      DafnyClientCodegenEdition.fromNumeric(editionNumeric);

    final List<StringNode> targetLangNodes = node
      .expectArrayMember("targetLanguages")
      .getElementsAs(StringNode.class);
    AtomicBoolean foundUnknownTargetLanguage = new AtomicBoolean(false);
    final Set<CodegenEngine.TargetLanguage> targetLanguages = targetLangNodes
      .stream()
      .flatMap(strNode ->
        switch (strNode.getValue().toUpperCase()) {
          case "JAVA" -> Stream.of(CodegenEngine.TargetLanguage.JAVA);
          case "DOTNET", "CSHARP", "CS" -> Stream.of(
            CodegenEngine.TargetLanguage.DOTNET
          );
          case "PYTHON" -> Stream.of(CodegenEngine.TargetLanguage.PYTHON);
          case "RUST" -> Stream.of(CodegenEngine.TargetLanguage.RUST);
          case "DAFNY" -> {
            LOGGER.error(
              "Dafny code is always generated, and shouldn't be specified explicitly"
            );
            foundUnknownTargetLanguage.set(true);
            yield Stream.empty();
          }
          default -> {
            LOGGER.error("Unknown target language: {}", strNode.getValue());
            foundUnknownTargetLanguage.set(true);
            yield Stream.empty();
          }
        }
      )
      .collect(Collectors.toSet());
    if (foundUnknownTargetLanguage.get()) {
      return Optional.empty();
    }
    if (targetLanguages.size() < targetLangNodes.size()) {
      LOGGER.error("Duplicate target languages specified; aborting");
      return Optional.empty();
    }

    final Optional<Path> buildRoot = findSmithyBuildJson(manifest.getBaseDir())
      .map(p -> p.getParent());
    final String includeDafnyFileStr = node
      .expectStringMember("includeDafnyFile")
      .getValue();
    final Path includeDafnyFile = Path.of(includeDafnyFileStr);
    final Path includeDafnyFileNormalized = buildRoot.isPresent() &&
      !includeDafnyFile.isAbsolute()
      ? buildRoot.get().resolve(includeDafnyFile).toAbsolutePath().normalize()
      : includeDafnyFile;
    if (Files.notExists(includeDafnyFileNormalized)) {
      LOGGER.warn(
        "Generated Dafny code may not compile because the includeDafnyFile could not be found: {}",
        includeDafnyFileNormalized
      );
    }

    // This is now optional since we can get it from dafny itself
    final DafnyVersion dafnyVersionString = node
      .getStringMember("dafnyVersion")
      .map(StringNode::getValue)
      .map(DafnyVersion::parse)
      .orElse(null);

    return Optional.of(
      new DafnyClientCodegenPluginSettings(
        edition,
        serviceId,
        targetLanguages,
        includeDafnyFileNormalized,
        dafnyVersionString
      )
    );
  }

  /**
   * Traverses up from the given start path,
   * searching for a "smithy-build.json" file and returning its path if found.
   */
  private static Optional<Path> findSmithyBuildJson(final Path start) {
    if (start == null || !start.isAbsolute()) {
      throw new IllegalArgumentException(
        "Start path must be non-null and absolute"
      );
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
