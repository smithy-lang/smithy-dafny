// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.smithy.dafny.codegen;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Collections;
import java.util.EnumSet;
import java.util.HashMap;
import java.util.Map;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import software.amazon.polymorph.CodegenEngine;
import software.amazon.polymorph.CodegenEngine.TargetLanguage;
import software.amazon.smithy.build.FileManifest;
import software.amazon.smithy.build.PluginContext;
import software.amazon.smithy.build.SmithyBuildPlugin;
import software.amazon.smithy.model.Model;

public final class DafnyClientCodegenPlugin implements SmithyBuildPlugin {

  private static final Logger LOGGER = LoggerFactory.getLogger(
    DafnyClientCodegenPlugin.class
  );

  @Override
  public String getName() {
    return "dafny-client-codegen";
  }

  @Override
  public void execute(PluginContext context) {
    final Model model = context.getModel();
    // TODO register generated files to allow to produce a proper manifest
    final FileManifest manifest = context.getFileManifest();
    final DafnyClientCodegenPluginSettings settings =
      DafnyClientCodegenPluginSettings
        .fromObject(context.getSettings(), manifest)
        .orElseThrow(() ->
          new RuntimeException("Invalid plugin settings; aborting")
        );

    final Map<TargetLanguage, Path> outputDirs = new HashMap<>();
    outputDirs.put(
      TargetLanguage.DAFNY,
      manifest.resolvePath(Paths.get("Model"))
    );
    settings.targetLanguages.forEach(lang -> {
      final Path dir =
        switch (lang) {
          case DOTNET -> Paths.get("runtimes", "net", "Generated");
          case JAVA -> Paths.get(
            "runtimes",
            lang.name().toLowerCase(),
            "src",
            "main",
            "smithy-generated"
          );
          case RUST -> Paths.get("runtimes", "rust");
          default -> throw new UnsupportedOperationException(
            lang + " is not yet supported"
          );
        };
      outputDirs.put(lang, manifest.resolvePath(dir));
    });
    final Path propertiesFile = manifest.resolvePath(
      Paths.get("project.properties")
    );

    // TODO remove when Java is properly supported
    if (settings.targetLanguages.contains(TargetLanguage.JAVA)) {
      LOGGER.warn(
        "smithy-dafny-codegen support for Java code generation is experimental and does not yet work for arbitrary service models"
      );
    }

    final CodegenEngine codegenEngine = new CodegenEngine.Builder()
      .withFromSmithyBuildPlugin(true)
      .withLibraryRoot(manifest.getBaseDir())
      .withServiceModel(model)
      // TODO generate code based on service closure, not namespace
      .withNamespaces(Collections.singleton(settings.serviceId.getNamespace()))
      .withDafnyVersion(settings.dafnyVersion)
      .withPropertiesFile(propertiesFile)
      .withTargetLangOutputDirs(outputDirs)
      .withAwsSdkStyle(true) // this plugin only generates AWS SDK-style code
      .withIncludeDafnyFile(settings.includeDafnyFile)
      .withGenerationAspects(
        EnumSet.of(
          CodegenEngine.GenerationAspect.PROJECT_FILES,
          CodegenEngine.GenerationAspect.CLIENT_CONSTRUCTORS
        )
      )
      .build();
    codegenEngine.run();
  }
}
