// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.smithy.dafny.codegen;

import software.amazon.polymorph.CodegenEngine;
import software.amazon.polymorph.CodegenEngine.TargetLanguage;
import software.amazon.smithy.build.FileManifest;
import software.amazon.smithy.build.PluginContext;
import software.amazon.smithy.build.SmithyBuildPlugin;
import software.amazon.smithy.model.Model;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Map;

public final class DafnyClientCodegenPlugin implements SmithyBuildPlugin {
    @Override
    public String getName() {
        return "dafny-client-codegen";
    }

    @Override
    public void execute(PluginContext context) {
        final Model model = context.getModel();
        final FileManifest manifest = context.getFileManifest();
        final DafnyClientCodegenPluginSettings settings = DafnyClientCodegenPluginSettings
                .fromObject(context.getSettings(), manifest)
                .orElseThrow(() -> new RuntimeException("Invalid plugin settings; aborting"));

        final Map<TargetLanguage, Path> outputDirs = new HashMap<>();
        outputDirs.put(TargetLanguage.DAFNY, manifest.resolvePath(Paths.get("Model")));
        settings.targetLanguages.forEach(lang -> {
            final Path dir = Paths.get("runtimes", lang.name().toLowerCase(), "Generated");
            outputDirs.put(lang, manifest.resolvePath(dir));
        });

        final CodegenEngine codegenEngine = new CodegenEngine.Builder()
                .withServiceModel(model)
                .withNamespace(settings.serviceId.getNamespace())
                .withTargetLangOutputDirs(outputDirs)
                .withAwsSdkStyle(true)  // this plugin only generates AWS SDK-style code
                .withIncludeDafnyFile(settings.includeDafnyFile)
                .withGenerateProjectFiles(true)
                .build();
        codegenEngine.run();
    }
}
