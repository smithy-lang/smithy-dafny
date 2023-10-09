// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph;

import com.fasterxml.jackson.core.JsonFactory;
import com.fasterxml.jackson.core.JsonProcessingException;
import com.fasterxml.jackson.databind.JsonNode;
import com.fasterxml.jackson.databind.ObjectMapper;
import java.io.IOException;
import java.nio.file.Files;
import java.util.Iterator;
import java.util.Map.Entry;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import software.amazon.polymorph.CodegenEngine.TargetLanguage;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject.AwsSdkVersion;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.build.FileManifest;
import software.amazon.smithy.build.PluginContext;
import software.amazon.smithy.dafny.codegen.DafnyClientCodegenPlugin;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.node.ObjectNode;
import software.amazon.smithy.model.shapes.ServiceShape;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.HashMap;
import java.util.Map;
import java.util.Optional;
import java.util.Arrays;

public class CodegenCli {
    private static final Logger LOGGER = LoggerFactory.getLogger(CodegenCli.class);

    public static void main(String[] args) {
        if (args.length == 0 || Arrays.asList(args).contains("-h")) {
            printHelpMessage();
            System.exit(0);
        }
        Optional<CliArguments> cliArgumentsOptional = Optional.empty();
        try {
            cliArgumentsOptional = CliArguments.parse(args);
        } catch (ParseException e) {
            LOGGER.error("Command-line arguments could not be parsed", e);
        }
        if (cliArgumentsOptional.isEmpty()) {
            printHelpMessage();
            System.exit(0);
        }
        final CliArguments cliArguments = cliArgumentsOptional.get();

        LOGGER.debug("Loading model from {}", cliArguments.modelPath);
        final ModelAssembler assembler = new ModelAssembler();
        assembler.addImport(cliArguments.modelPath);
        Arrays.stream(cliArguments.dependentModelPaths).forEach(assembler::addImport);
        // Discover models from the classpath (e.g. models of library-defined traits)
        assembler.discoverModels();
        final Model serviceModel = assembler.assemble().unwrap();

        // If Smithy ever lets us configure this:
        // https://github.com/smithy-lang/smithy/blob/f598b87c51af5943686e38706847a5091fe718da/smithy-model/src/main/java/software/amazon/smithy/model/loader/ModelLoader.java#L76
        // We can remove this log statement.
        // (Alternatively, We could inline `addImport`,
        // and ignore dfy & md files. Link to `addImport` below)
        // https://github.com/smithy-lang/smithy/blob/f598b87c51af5943686e38706847a5091fe718da/smithy-model/src/main/java/software/amazon/smithy/model/loader/ModelAssembler.java#L256-L281
        LOGGER.info("End annoying Smithy \"No ModelLoader was able to load\" warnings.\n\n");

        final Map<TargetLanguage, Path> outputDirs = new HashMap<>();
        cliArguments.outputDafnyDir.ifPresent(path -> outputDirs.put(TargetLanguage.DAFNY, path));
        cliArguments.outputJavaDir.ifPresent(path -> outputDirs.put(TargetLanguage.JAVA, path));
        cliArguments.outputDotnetDir.ifPresent(path -> outputDirs.put(TargetLanguage.DOTNET, path));
        cliArguments.outputPythonDir.ifPresent(path -> outputDirs.put(TargetLanguage.PYTHON, path));

        ObjectNode.Builder objectNodeBuilder = ObjectNode.builder();
        // If a smithy-build.json is provided, parse it for settings to pipe into PluginContext
        if (cliArguments.smithyBuildFilePath.isPresent()) {
            String json;
            try {
                json = Files.readString(cliArguments.smithyBuildFilePath.get());
            } catch (IOException e) {
                throw new RuntimeException("IOException while reading smithy-build.json", e);
            }

            JsonFactory factory = new JsonFactory();
            ObjectMapper mapper = new ObjectMapper(factory);
            JsonNode rootNode;
            try {
                rootNode = mapper.readTree(json);
            } catch (JsonProcessingException e) {
                throw new RuntimeException("JsonProcessingException while processing smithy-build.json", e);
            }

            Iterator<Entry<String, JsonNode>> attributes = rootNode
                // MUST be "plugins" per smithy-build.json spec
                .findValue("plugins")
                // MUST be same plugin name as the Dafny codegen plugin
                .findValue(DafnyClientCodegenPlugin.pluginName).fields();

            while(attributes.hasNext()) {
                Entry<String, JsonNode> entry = attributes.next();
                // Remove leading and trailing " on the attribute value before adding it to settings
                objectNodeBuilder.withMember(entry.getKey(), entry.getValue().toString().replace("\"", ""));
            }
        }

        final PluginContext pluginContext = PluginContext.builder()
            .model(serviceModel)
            .fileManifest(FileManifest.create(cliArguments.outputPythonDir().orElse(cliArguments.modelPath)))
            .settings(objectNodeBuilder.build())
            .build();

        final CodegenEngine.Builder engineBuilder = new CodegenEngine.Builder()
                .withServiceModel(serviceModel)
                .withDependentModelPaths(cliArguments.dependentModelPaths)
                .withNamespace(cliArguments.namespace)
                .withTargetLangOutputDirs(outputDirs)
                .withAwsSdkStyle(cliArguments.awsSdkStyle)
                .withPluginContext(pluginContext)
                .withLocalServiceTest(cliArguments.localServiceTest);
        cliArguments.javaAwsSdkVersion.ifPresent(engineBuilder::withJavaAwsSdkVersion);
        cliArguments.includeDafnyFile.ifPresent(engineBuilder::withIncludeDafnyFile);
        final CodegenEngine engine = engineBuilder.build();
        engine.run();
    }

    private static Options getCliOptions() {
        return new Options()
          .addOption(Option.builder("h")
            .longOpt("help")
            .desc("print help message")
            .build())
          .addOption(Option.builder("m")
            .longOpt("model")
            .desc("directory for the model file[s] (.smithy or json format).")
            .hasArg()
            .required()
            .build())
          .addOption(Option.builder()
            .longOpt("smithy-build")
            .desc("path to the smithy-build.json file")
            .hasArg()
            .build())
          .addOption(Option.builder("d")
            .longOpt("dependent-model")
            .desc("directory for dependent model file[s] (.smithy format)")
            .hasArg()
            .required()
            .build())
          .addOption(Option.builder("n")
            .longOpt("namespace")
            .desc("smithy namespace to generate code for, such as 'com.foo'")
            .hasArg()
            .required()
            .build())
          .addOption(Option.builder()
            .longOpt("output-dotnet")
            .desc("<optional> output directory for generated .NET files")
            .hasArg()
            .build())
          .addOption(Option.builder()
            .longOpt("output-java")
            .desc("<optional> output directory for generated Java files")
            .hasArg()
            .build())
          .addOption(Option.builder()
            .longOpt("output-python")
            .desc("<optional> output directory for generated Python files")
            .hasArg()
            .build())
          .addOption(Option.builder()
            .longOpt("java-aws-sdk-version")
            .desc("<optional> AWS SDK for Java version to use: v1, or v2 (default)")
            .hasArg()
            .build())
          .addOption(Option.builder()
            .longOpt("aws-sdk")
            .desc("<optional> generate AWS SDK-style API and shims")
            .build())
          .addOption(Option.builder()
            .longOpt("local-service-test")
            .desc("<optional> generate Dafny that tests a local service")
            .build())
          .addOption(Option.builder()
            .longOpt("output-dafny")
            .desc("<optional> output directory for generated Dafny code")
            .hasArg()
            .optionalArg(true)
            .build())
          .addOption(Option.builder()
            .longOpt("include-dafny")
            .desc("<optional> files to be include in the generated Dafny")
            .hasArg()
            .build());
    }

    private static void printHelpMessage() {
        new HelpFormatter().printHelp("smithy-dafny-codegen-cli", getCliOptions());
    }

    private record CliArguments(
            Path modelPath,
            Optional<Path> smithyBuildFilePath,
            Path[] dependentModelPaths,
            String namespace,
            Optional<Path> outputDotnetDir,
            Optional<Path> outputJavaDir,
            Optional<Path> outputPythonDir,
            Optional<Path> outputDafnyDir,
            Optional<AwsSdkVersion> javaAwsSdkVersion,
            Optional<Path> includeDafnyFile,
            boolean awsSdkStyle,
            boolean localServiceTest
    ) {
        /**
         * @param args arguments to parse
         * @return parsed arguments, or {@code Optional.empty()} if help should be printed
         * @throws ParseException if command line arguments are invalid
         */
        static Optional<CliArguments> parse(String[] args) throws ParseException {
            final DefaultParser parser = new DefaultParser();
            final CommandLine commandLine = parser.parse(getCliOptions(), args);
            if (commandLine.hasOption("h")) {
                printHelpMessage();
                return Optional.empty();
            }

            final Path modelPath = Path.of(commandLine.getOptionValue('m'));
            final Optional<Path> smithyBuildFilePath = Optional.ofNullable(commandLine.getOptionValue("smithy-build"))
                    .map(Paths::get);

            final Path[] dependentModelPaths = Arrays
              .stream(commandLine.getOptionValues('d'))
              .map(Path::of)
              .toArray(Path[]::new);

            final String namespace = commandLine.getOptionValue('n');

            Optional<Path> outputDafnyDir = Optional.ofNullable(commandLine.getOptionValue("output-dafny"))
                    .map(Paths::get);
            if (commandLine.hasOption("output-dafny") && outputDafnyDir.isEmpty()) {
                LOGGER.warn("Using `output-dafny` without providing a Path argument is deprecated and will be removed.");
                LOGGER.warn("Assuming Dafny should be written to Model path.");
                outputDafnyDir = Optional.of(Paths.get(commandLine.getOptionValue("m")));
            }

            final Optional<Path> outputJavaDir = Optional.ofNullable(commandLine.getOptionValue("output-java"))
                    .map(Paths::get);
            final Optional<Path> outputDotnetDir = Optional.ofNullable(commandLine.getOptionValue("output-dotnet"))
                    .map(Paths::get);
            final Optional<Path> outputPythonDir = Optional.ofNullable(commandLine.getOptionValue("output-python"))
                .map(Paths::get);

            boolean localServiceTest = commandLine.hasOption("local-service-test");
            final boolean awsSdkStyle = commandLine.hasOption("aws-sdk");

            Optional<AwsSdkVersion> javaAwsSdkVersion = Optional.empty();
            if (commandLine.hasOption("java-aws-sdk-version")) {
                final String versionStr = commandLine.getOptionValue("java-aws-sdk-version").trim().toUpperCase();
                try {
                    javaAwsSdkVersion = Optional.of(AwsSdkVersion.valueOf(versionStr));
                } catch (IllegalArgumentException ex) {
                    LOGGER.error("Unknown Java AWS SDK version {}", versionStr);
                    throw ex;
                }
            }

            Optional<Path> includeDafnyFile = Optional.empty();
            if (outputDafnyDir.isPresent()) {
                includeDafnyFile = Optional.of(Paths.get(commandLine.getOptionValue("include-dafny")));
            }

            return Optional.of(new CliArguments(
                    modelPath, smithyBuildFilePath, dependentModelPaths, namespace,
                    outputDotnetDir, outputJavaDir, outputPythonDir, outputDafnyDir,
                    javaAwsSdkVersion, includeDafnyFile, awsSdkStyle,
                    localServiceTest
            ));
        }
    }
}
