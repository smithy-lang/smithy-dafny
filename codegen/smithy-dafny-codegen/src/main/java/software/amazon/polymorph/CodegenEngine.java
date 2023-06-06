// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph;

import com.google.common.base.Strings;
import com.google.common.collect.ImmutableMap;
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
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.utils.IOUtils;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.selector.Selector;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.utils.IoUtils;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;

public class CodegenEngine {
    private static final Logger LOGGER = LoggerFactory.getLogger(CodegenEngine.class);

    private final Path[] dependentModelPaths;
    private final String namespace;
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
            final Map<TargetLanguage, Path> targetLangOutputDirs,
            final AwsSdkVersion javaAwsSdkVersion,
            final Optional<Path> includeDafnyFile,
            final boolean awsSdkStyle,
            final boolean localServiceTest,
            final boolean generateProjectFiles
    ) {
        // To be provided to constructor
        this.dependentModelPaths = dependentModelPaths;
        this.namespace = namespace;
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
     * and idempotent with respect to the file system.
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
                default -> throw new UnsupportedOperationException("Cannot generate code for target language %s"
                        .formatted(lang.name()));
            }
        }
    }

    private void generateDafny(final Path outputDir) {
        List<String> supportedShapes = awsSdkStyle ? COMMON_SUPPORTED_SHAPES : SUPPORTED_SHAPES_NON_AWS_SDK_STYLE;
        List<String> supportedTraits = awsSdkStyle ? SUPPORTED_TRAITS_AWS_SDK_STYLE : SUPPORTED_TRAITS_NON_AWS_SDK_STYLE;
        checkForUnsupportedFeatures(supportedShapes, supportedTraits);

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

    public static class Builder {
        private Model serviceModel;
        private Path[] dependentModelPaths;
        private String namespace;
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
    }

    private static final List<String> COMMON_SUPPORTED_SHAPES = List.of(
            "boolean",
            "blob",
            "double",
            "integer",
            "list",
            "long",
            "map",
            "member",
            "operation",
            "string",
            "service",
            "structure",
            "timestamp",
            "union"
    );

    private static final List<String> SUPPORTED_SHAPES_NON_AWS_SDK_STYLE =
            Stream.concat(
                    COMMON_SUPPORTED_SHAPES.stream(),
                    Stream.of(
                            // Playing it safe and not claiming to support this in SDK style mode yet,
                            // since we might be generating code that only makes sense for local services.
                            "resource"
                    )).toList();

    private static final List<String> COMMON_SUPPORTED_TRAITS = List.of(
            "smithy.api#box",
            "smithy.api#default",
            "smithy.api#documentation",
            "smithy.api#error",
            "smithy.api#enum",
            "smithy.api#idempotencyToken",
            "smithy.api#input",
            "smithy.api#length",
            "smithy.api#output",
            "smithy.api#pattern",
            "smithy.api#required",
            "smithy.api#range",
            "smithy.api#readonly",
            "smithy.api#sensitive",
            "smithy.api#uniqueItems"
    );

    private static final List<String> SUPPORTED_TRAITS_NON_AWS_SDK_STYLE =
            Stream.concat(
                    COMMON_SUPPORTED_TRAITS.stream(),
                    Stream.of(
                            // For those that literally can't be used for non-local services,
                            // We probably want model validation to forbid them instead,
                            "aws.polymorph#extendable",
                            "aws.polymorph#localService",
                            "aws.polymorph#dafnyUtf8Bytes",
                            "aws.polymorph#javadoc",
                            "aws.polymorph#positional",
                            "aws.polymorph#reference"
                    )).toList();

    private static final List<String> SUPPORTED_TRAITS_AWS_SDK_STYLE =
            Stream.concat(
                    COMMON_SUPPORTED_TRAITS.stream(),
                    Stream.of(
                            // Most of these are protocol details handled by the wrapped SDKs
                            // and not relevant for SDK consumers.
                            "aws.api#clientEndpointDiscovery",
                            "aws.api#clientDiscoveredEndpoint",
                            "aws.api#service",
                            "aws.auth#sigv4",
                            "aws.protocols#awsJson1_0",
                            "aws.protocols#awsJson1_1",
                            "aws.protocols#awsQuery",
                            "aws.protocols#awsQueryError",
                            "smithy.api#deprecated",
                            "smithy.api#paginated",
                            "smithy.api#suppress",
                            "smithy.api#httpError",
                            "smithy.api#title",
                            "smithy.api#xmlFlattened",
                            "smithy.api#xmlName",
                            "smithy.api#xmlNamespace",
                            "smithy.rules#endpointTests",
                            "smithy.rules#endpointRuleSet",
                            // We don't really support this yet, since it implies extra API
                            // methods we don't generate, but at least we don't generate incorrect code.
                            "smithy.waiters#waitable"
                    )).toList();

    private void checkForUnsupportedFeatures(Collection<String> supportedShapes, Collection<String> supportedTraits) {
        String selectorExpr =
                "[id=" + serviceShape.getId() + "] \n" +
                        ":is(*, ~> *) \n" +
                        ":not(\n" +
                            ":is(" + String.join(", ", supportedShapes) + ") " +
                            "$supportedTraits(:root([id = " + String.join(", ", supportedTraits) + "])) " +
                            "[@: @{trait|(keys)} {<} @{var|supportedTraits|id}]" +
                        ")";

        Set<Shape> notSupported = Selector.parse(selectorExpr).select(model);

        if (!notSupported.isEmpty()) {
            String message = "The following shapes in the service's closure are not supported: \n" +
                    notSupported.stream()
                                .map(shape -> unsupportedShapeLine(shape, supportedShapes, supportedTraits))
                                .collect(Collectors.joining("\n"));
            throw new IllegalArgumentException(message);
        }
    }

    private String unsupportedShapeLine(Shape shape, Collection<String> supportedShapes, Collection<String> supportedTraits) {
        StringBuilder builder = new StringBuilder();
        builder.append(shape.toString());
        builder.append("\n");
        if (!supportedShapes.contains(shape.getType().toString())) {
            builder.append(" - (shape type `" + shape.getType().toString() + "` is not supported)");
        }
        for (var trait : shape.getAllTraits().keySet()) {
            if (!supportedTraits.contains(trait.toShapeId().toString())) {
                builder.append(" - (trait `" + trait.toShapeId() + "` is not supported)");
            }
        }
        return builder.toString();
    }
}
