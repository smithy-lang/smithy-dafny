// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph;

import com.google.common.base.Strings;
import com.google.common.collect.ImmutableMap;
import java.util.Locale;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import software.amazon.polymorph.smithydafny.DafnyApiCodegen;
import software.amazon.polymorph.smithydotnet.AwsSdkShimCodegen;
import software.amazon.polymorph.smithydotnet.AwsSdkTypeConversionCodegen;
import software.amazon.polymorph.smithydotnet.ServiceCodegen;
import software.amazon.polymorph.smithydotnet.ShimCodegen;
import software.amazon.polymorph.smithydotnet.TypeConversionCodegen;
import software.amazon.polymorph.smithydotnet.localServiceWrapper.LocalServiceWrappedCodegen;
import software.amazon.polymorph.smithydotnet.localServiceWrapper.LocalServiceWrappedConversionCodegen;
import software.amazon.polymorph.smithydotnet.localServiceWrapper.LocalServiceWrappedShimCodegen;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject.AwsSdkVersion;
import software.amazon.polymorph.smithyjava.generator.awssdk.v1.JavaAwsSdkV1;
import software.amazon.polymorph.smithyjava.generator.awssdk.v2.JavaAwsSdkV2;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.polymorph.smithyjava.generator.library.TestJavaLibrary;
import software.amazon.polymorph.smithypython.awssdk.extensions.DafnyPythonAwsSdkClientCodegenPlugin;
import software.amazon.polymorph.smithypython.localservice.extensions.DafnyPythonLocalServiceClientCodegenPlugin;
import software.amazon.polymorph.smithypython.wrappedlocalservice.extensions.DafnyPythonWrappedLocalServiceClientCodegenPlugin;
import software.amazon.polymorph.utils.IOUtils;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.build.FileManifest;
import software.amazon.smithy.build.PluginContext;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.node.ObjectNode;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.utils.IoUtils;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;

public class CodegenEngine {
    private static final Logger LOGGER = LoggerFactory.getLogger(CodegenEngine.class);

    private final Path[] dependentModelPaths;
    private final String namespace;
    private final Optional<String> pythonModuleName;
    private final Map<TargetLanguage, Path> targetLangOutputDirs;
    // refactor this to only be required if generating Java
    private final AwsSdkVersion javaAwsSdkVersion;
    private final Optional<Path> includeDafnyFile;
    private final boolean awsSdkStyle;
    private final boolean localServiceTest;
    private final boolean generateProjectFiles;

    // To be initialized in constructor
    private final Model model;
    private final ServiceShape serviceShape;

    /**
     * This should only be called by {@link Builder#build()},
     * which is responsible for validating that the arguments are non-null,
     * are mutually compatible, etc.
     */
    private CodegenEngine(
            final Model serviceModel,
            final Path[] dependentModelPaths,
            final String namespace,
            final Optional<String> pythonModuleName,
            final Map<TargetLanguage, Path> targetLangOutputDirs,
            final AwsSdkVersion javaAwsSdkVersion,
            final Optional<Path> includeDafnyFile,
            final boolean awsSdkStyle,
            final boolean localServiceTest,
            final boolean generateProjectFiles
    ) {
        // To be provided to constructor
        // TODO-Python: Refactor by passing module_name into CLI?

        this.dependentModelPaths = dependentModelPaths;
        this.namespace = namespace;
        this.pythonModuleName = pythonModuleName;
        this.targetLangOutputDirs = targetLangOutputDirs;
        this.javaAwsSdkVersion = javaAwsSdkVersion;
        this.includeDafnyFile = includeDafnyFile;
        this.awsSdkStyle = awsSdkStyle;
        this.localServiceTest = localServiceTest;
        this.generateProjectFiles = generateProjectFiles;

        this.model = this.awsSdkStyle
                // TODO: move this into a DirectedCodegen.customizeBeforeShapeGeneration implementation
                ? ModelUtils.addMissingErrorMessageMembers(serviceModel)
                : serviceModel;

        this.serviceShape = ModelUtils.serviceFromNamespace(this.model, this.namespace);
    }

    /**
     * Executes code generation for the configured language(s).
     * This method is designed to be internally stateless
     * and idempotent with respect with respect to the file system.
     */
    public void run() {
        try {
            LOGGER.debug("Ensuring target-language output directories exist");
            for (final Path dir : this.targetLangOutputDirs.values()) {
                Files.createDirectories(dir);
            }
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(1);
        }

        for (final TargetLanguage lang : targetLangOutputDirs.keySet()) {
            final Path outputDir = targetLangOutputDirs.get(lang).toAbsolutePath().normalize();
            switch (lang) {
                case DAFNY -> generateDafny(outputDir);
                case JAVA -> generateJava(outputDir);
                case DOTNET -> generateDotnet(outputDir);
                case PYTHON -> generatePython();
                default -> throw new UnsupportedOperationException("Cannot generate code for target language %s"
                        .formatted(lang.name()));
            }
        }
    }

    private void generateDafny(final Path outputDir) {
        // Validated by builder, but check again
        assert this.includeDafnyFile.isPresent();
        final DafnyApiCodegen dafnyApiCodegen = new DafnyApiCodegen(
                model,
                serviceShape,
                outputDir,
                this.includeDafnyFile.get(),
                this.dependentModelPaths,
                this.awsSdkStyle);

        if (this.localServiceTest) {
            IOUtils.writeTokenTreesIntoDir(
                    dafnyApiCodegen.generateWrappedAbstractServiceModule(outputDir),
                    outputDir);
            LOGGER.info("Dafny that tests a local service generated in {}", outputDir);
        } else {
            IOUtils.writeTokenTreesIntoDir(dafnyApiCodegen.generate(), outputDir);
            LOGGER.info("Dafny code generated in {}", outputDir);
        }
    }

    private void generateJava(final Path outputDir) {
        if (this.awsSdkStyle) {
            switch (this.javaAwsSdkVersion) {
                case V1 -> javaAwsSdkV1(outputDir);
                case V2 -> javaAwsSdkV2(outputDir);
            }
        } else if (this.localServiceTest) {
            javaWrappedLocalService(outputDir);
        } else {
            javaLocalService(outputDir);
        }
    }

    private void javaLocalService(final Path outputDir) {
        final JavaLibrary javaLibrary = new JavaLibrary(this.model, this.serviceShape, this.javaAwsSdkVersion);
        IOUtils.writeTokenTreesIntoDir(javaLibrary.generate(), outputDir);
        LOGGER.info("Java code generated in {}", outputDir);
    }

    private void javaWrappedLocalService(final Path outputDir) {
        final TestJavaLibrary testJavaLibrary = new TestJavaLibrary(model, serviceShape, this.javaAwsSdkVersion);
        IOUtils.writeTokenTreesIntoDir(testJavaLibrary.generate(), outputDir);
        LOGGER.info("Java that tests a local service generated in {}", outputDir);
    }

    private void javaAwsSdkV1(Path outputDir) {
        final JavaAwsSdkV1 javaShimCodegen = JavaAwsSdkV1.createJavaAwsSdkV1(this.serviceShape, this.model);
        IOUtils.writeTokenTreesIntoDir(javaShimCodegen.generate(), outputDir);
        LOGGER.info("Java V1 code generated in {}", outputDir);
    }

    private void javaAwsSdkV2(final Path outputDir) {
        final JavaAwsSdkV2 javaV2ShimCodegen = JavaAwsSdkV2.createJavaAwsSdkV2(serviceShape, model);
        IOUtils.writeTokenTreesIntoDir(javaV2ShimCodegen.generate(), outputDir);
        LOGGER.info("Java V2 code generated in {}", outputDir);
    }

    private void generateDotnet(final Path outputDir) {
        if (this.awsSdkStyle) {
            netAwsSdk(outputDir);
            if (this.generateProjectFiles) {
                netAwsSdkProjectFiles(outputDir);
            }
        } else if (this.localServiceTest) {
            netWrappedLocalService(outputDir);
        } else {
            netLocalService(outputDir);
        }
    }

    private void netLocalService(final Path outputDir) {
        final ServiceCodegen service = new ServiceCodegen(model, serviceShape);
        IOUtils.writeTokenTreesIntoDir(service.generate(), outputDir);

        final ShimCodegen shim = new ShimCodegen(model, serviceShape);
        IOUtils.writeTokenTreesIntoDir(shim.generate(), outputDir);

        final TypeConversionCodegen conversion = new TypeConversionCodegen(model, serviceShape);
        IOUtils.writeTokenTreesIntoDir(conversion.generate(), outputDir);
        LOGGER.info(".NET code generated in {}", outputDir);
    }

    private void netWrappedLocalService(final Path outputDir) {
        final LocalServiceWrappedCodegen service = new LocalServiceWrappedCodegen(model, serviceShape);
        IOUtils.writeTokenTreesIntoDir(service.generate(), outputDir);

        final LocalServiceWrappedShimCodegen wrappedShim = new LocalServiceWrappedShimCodegen(model, serviceShape);
        IOUtils.writeTokenTreesIntoDir(wrappedShim.generate(), outputDir);

        final TypeConversionCodegen conversion = new LocalServiceWrappedConversionCodegen(model, serviceShape);
        IOUtils.writeTokenTreesIntoDir(conversion.generate(), outputDir);
        LOGGER.info(".NET that tests a local service generated in {}", outputDir);
    }

    private void netAwsSdk(final Path outputDir) {
        final AwsSdkShimCodegen dotnetShimCodegen = new AwsSdkShimCodegen(model, serviceShape);
        IOUtils.writeTokenTreesIntoDir(dotnetShimCodegen.generate(), outputDir);

        final TypeConversionCodegen conversion = new AwsSdkTypeConversionCodegen(model, serviceShape);
        IOUtils.writeTokenTreesIntoDir(conversion.generate(), outputDir);
        LOGGER.info(".NET code generated in {}", outputDir);
    }

    private void netAwsSdkProjectFiles(final Path outputDir) {
        final String sdkId = this.serviceShape.expectTrait(ServiceTrait.class).getSdkId();

        final Path includeDafnyFile = this.includeDafnyFile.orElseThrow(
                () -> new IllegalStateException("includeDafnyFile required when generating .NET project files"));
        // Assumes that includeDafnyFile is at StandardLibrary/src/Index.dfy
        // TODO be smarter about finding the StandardLibrary path
        final Path stdLibPath = outputDir.relativize(includeDafnyFile.resolve("../.."));

        final String csprojTemplate = IoUtils.readUtf8Resource(
                this.getClass(), "/templates/AwsSdkProject.csproj.template");
        final String csprojText = csprojTemplate
                .replace("%SDK_ID%", sdkId)
                .replace("%STDLIB_PATH%", stdLibPath.toString());
        IOUtils.writeToFile(csprojText, outputDir.resolve(sdkId + ".csproj").toFile());

        // TODO generate Makefile

        LOGGER.info(".NET project files generated in {}", outputDir);
    }

    private void generatePython() {
        ObjectNode.Builder pythonSettingsBuilder = ObjectNode.builder()
            .withMember("service", serviceShape.getId().toString())

            // TODO-Python: `module` SHOULD be configured within the `smithy-build.json` file;
            // possibly at `dafny-client-codegen.targetLanguages.python.moduleVersion`.
            // This is Smithy-Python specific configuration.
            // This dictates the name of the generated Python package.
            // TODO: This depends on Dafny extending the `dafny-client-codegen.targetLanguages` key
            // to support storing language-specific configuration.
            // For now, assume `module` is a slight transformation of the model namespace.
            .withMember("module", pythonModuleName.get())

            // TODO-Python: `moduleVersion` SHOULD be configured within the `smithy-build.json` file;
            // possibly at `dafny-client-codegen.targetLanguages.python.moduleVersion`.
            // This is Smithy-Python specific configuration.
            // This dictates the version of the smithygenerated code, but this is unused;
            //   Polymorph wraps the smithygenerated code in a module with an independent
            //   module version.
            // TODO: This depends on Dafny extending the `dafny-client-codegen.targetLanguages` key
            // to support storing language-specific configuration.
            // For now, hardcode this to 0.0.1.
            .withMember("moduleVersion", "0.0.1");

        final PluginContext pluginContext = PluginContext.builder()
            .model(model)
            .fileManifest(FileManifest.create(targetLangOutputDirs.get(TargetLanguage.PYTHON)))
            .settings(pythonSettingsBuilder.build())
            .build();

        if (this.awsSdkStyle) {
            DafnyPythonAwsSdkClientCodegenPlugin dafnyPythonAwsSdkClientCodegenPlugin
                = new DafnyPythonAwsSdkClientCodegenPlugin();
            dafnyPythonAwsSdkClientCodegenPlugin.execute(pluginContext);
        } else if (this.localServiceTest) {
            DafnyPythonWrappedLocalServiceClientCodegenPlugin pythonClientCodegenPlugin = new DafnyPythonWrappedLocalServiceClientCodegenPlugin();
            pythonClientCodegenPlugin.execute(pluginContext);
        } else {
            DafnyPythonLocalServiceClientCodegenPlugin pythonClientCodegenPlugin = new DafnyPythonLocalServiceClientCodegenPlugin();
            pythonClientCodegenPlugin.execute(pluginContext);
        }
    }

    public static class Builder {
        private Model serviceModel;
        private Path[] dependentModelPaths;
        private String namespace;
        private String pythonModuleName;
        private Map<TargetLanguage, Path> targetLangOutputDirs;
        private AwsSdkVersion javaAwsSdkVersion = AwsSdkVersion.V2;
        private Path includeDafnyFile;
        private boolean awsSdkStyle = false;
        private boolean localServiceTest = false;
        private boolean generateProjectFiles = false;

        public Builder() {}

        /**
         * Sets the directory in which to search for model files(s) containing the desired service.
         */
        public Builder withServiceModel(final Model serviceModel) {
            this.serviceModel = serviceModel;
            return this;
        }

        /**
         * Sets the directories in which to search for dependent model file(s).
         */
        public Builder withDependentModelPaths(final Path[] dependentModelPaths) {
            this.dependentModelPaths = dependentModelPaths;
            return this;
        }

        /**
         * Sets the Smithy namespace for which to generate code (e.g. "com.foo").
         */
        public Builder withNamespace(final String namespace) {
            this.namespace = namespace;
            return this;
        }

        /**
         * Sets the Python module name for any generated Python code.
         */
        public Builder withPythonModuleName(final String pythonModuleName) {
            this.pythonModuleName = pythonModuleName;
            return this;
        }


        /**
         * Sets the target language(s) for which to generate code,
         * along with the directory(-ies) into which to output each language's generated code.
         */
        public Builder withTargetLangOutputDirs(final Map<TargetLanguage, Path> targetLangOutputDirs) {
            this.targetLangOutputDirs = targetLangOutputDirs;
            return this;
        }

        /**
         * Sets the version of the AWS SDK for Java for which generated code should be compatible.
         * This has no effect unless the engine is configured to generate Java code.
         */
        public Builder withJavaAwsSdkVersion(final AwsSdkVersion javaAwsSdkVersion) {
            this.javaAwsSdkVersion = javaAwsSdkVersion;
            return this;
        }

        /**
         * Sets a file to be included in the generated Dafny code.
         */
        public Builder withIncludeDafnyFile(final Path includeDafnyFile) {
            this.includeDafnyFile = includeDafnyFile;
            return this;
        }

        /**
         * Sets whether codegen will generate AWS SDK-compatible API and shims.
         */
        public Builder withAwsSdkStyle(final boolean awsSdkStyle) {
            this.awsSdkStyle = awsSdkStyle;
            return this;
        }

        /**
         * Sets whether codegen will generate Dafny code to test a local service.
         */
        public Builder withLocalServiceTest(final boolean localServiceTest) {
            this.localServiceTest = localServiceTest;
            return this;
        }

        /**
         * Sets whether codegen will generate project files,
         * including a Makefile and target-language specific build configuration.
         */
        public Builder withGenerateProjectFiles(final boolean generateProjectFiles) {
            this.generateProjectFiles = generateProjectFiles;
            return this;
        }

        public CodegenEngine build() {
            final Model serviceModel = Objects.requireNonNull(this.serviceModel);
            final Path[] dependentModelPaths = this.dependentModelPaths == null
                    ? new Path[] {}
                    : this.dependentModelPaths.clone();
            if (Strings.isNullOrEmpty(this.namespace)) {
                throw new IllegalStateException("No namespace provided");
            }

            final Optional<String> pythonModuleName = Optional.ofNullable(this.pythonModuleName);

            final Map<TargetLanguage, Path> targetLangOutputDirsRaw = Objects.requireNonNull(this.targetLangOutputDirs);
            targetLangOutputDirsRaw.replaceAll((_lang, path) -> path.toAbsolutePath().normalize());
            final Map<TargetLanguage, Path> targetLangOutputDirs = ImmutableMap.copyOf(targetLangOutputDirsRaw);

            final AwsSdkVersion javaAwsSdkVersion = Objects.requireNonNull(this.javaAwsSdkVersion);

            if (targetLangOutputDirs.containsKey(TargetLanguage.DAFNY)
                    && this.includeDafnyFile == null) {
                throw new IllegalStateException("includeDafnyFile is required when generating Dafny code");
            }
            final Optional<Path> includeDafnyFile = Optional.ofNullable(this.includeDafnyFile)
                    .map(path -> path.toAbsolutePath().normalize());

            if (this.awsSdkStyle && this.localServiceTest) {
                throw new IllegalStateException(
                        "Cannot generate AWS SDK style code, and test a local service, at the same time");
            }

            return new CodegenEngine(
                    serviceModel,
                    dependentModelPaths,
                    this.namespace,
                    pythonModuleName,
                    targetLangOutputDirs,
                    javaAwsSdkVersion,
                    includeDafnyFile,
                    this.awsSdkStyle,
                    this.localServiceTest,
                    this.generateProjectFiles
            );
        }
    }

    public enum TargetLanguage {
        DAFNY,
        JAVA,
        DOTNET,
        PYTHON,
    }
}
