// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph;
import software.amazon.polymorph.utils.ModelUtils;

import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import software.amazon.polymorph.smithydafny.DafnyApiCodegen;
import software.amazon.polymorph.smithydotnet.AwsSdkShimCodegen;
import software.amazon.polymorph.smithydotnet.AwsSdkTypeConversionCodegen;
import software.amazon.polymorph.smithydotnet.ServiceCodegen;
import software.amazon.polymorph.smithydotnet.ShimCodegen;
import software.amazon.polymorph.smithydotnet.TypeConversionCodegen;
import software.amazon.polymorph.smithyjava.generator.awssdk.AwsSdk;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.shapes.ServiceShape;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Map;
import java.util.Optional;
import java.util.Arrays;

public class CodegenCli {
    private static final Logger logger = LoggerFactory.getLogger(CodegenCli.class);

    public static void main(String[] args) {
        Optional<CliArguments> cliArgumentsOptional = Optional.empty();
        try {
            cliArgumentsOptional = CliArguments.parse(args);
        } catch (ParseException e) {
            logger.error("Command-line arguments could not be parsed", e);
        }
        if (cliArgumentsOptional.isEmpty()) {
            printHelpMessage();
            System.exit(0);
        }
        final CliArguments cliArguments = cliArgumentsOptional.get();

        final Path outputDotnetDir = cliArguments.outputDotnetDir;
        final Path outputJavaDir = cliArguments.outputJavaDir;
        try {
            Files.createDirectories(outputDotnetDir);
            Files.createDirectories(outputJavaDir);
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(1);
        }

        final ModelAssembler assembler = new ModelAssembler();

        assembler.addImport(cliArguments.modelPath);
        Arrays
          .stream(cliArguments.dependentModelPaths)
          .forEach(path -> assembler.addImport(path));

        final Model model = assembler
          .assemble()
          .unwrap();

        final ServiceShape serviceShape = ModelUtils.serviceFromNamespace(model, cliArguments.namespace);

        if (cliArguments.awsSdkStyle) {
            final AwsSdkShimCodegen shimCodegen = new AwsSdkShimCodegen(
              model,
              serviceShape,
              cliArguments.dependentModelPaths
            );
            final AwsSdk javaShimCodegen = new AwsSdk(serviceShape, model);
            writeTokenTreesIntoDir(shimCodegen.generate(), outputDotnetDir);
            writeTokenTreesIntoDir(javaShimCodegen.generate(), outputDotnetDir);
            logger.info("Java code generated in {}", cliArguments.outputJavaDir);
        } else {
            final ServiceCodegen serviceCodegen = new ServiceCodegen(model, serviceShape);
            writeTokenTreesIntoDir(serviceCodegen.generate(), outputDotnetDir);

            final ShimCodegen shimCodegen = new ShimCodegen(model, serviceShape);
            writeTokenTreesIntoDir(shimCodegen.generate(), outputDotnetDir);

            logger.warn("Smithy-Polymorph only supports Java code generation for AWS-SDK Style code");
        }
        
        final DafnyApiCodegen dafnyApiCodegen = new DafnyApiCodegen(
          model,
          serviceShape,
          cliArguments.modelPath,
          cliArguments.dependentModelPaths
        );
        // The Smithy model and the Dafny code are expected to be in the same location.
        // This simplifies the process of including the various Dafny files.
        writeTokenTreesIntoDir(dafnyApiCodegen.generate(), cliArguments.modelPath);

        final TypeConversionCodegen typeConversionCodegen = cliArguments.awsSdkStyle
                ? new AwsSdkTypeConversionCodegen(model, serviceShape)
                : new TypeConversionCodegen(model, serviceShape);
        writeTokenTreesIntoDir(typeConversionCodegen.generate(), outputDotnetDir);

        logger.info(".NET code generated in {}", cliArguments.outputDotnetDir);
        logger.info("Dafny code generated in {}", cliArguments.modelPath);
    }

    private static Options getCliOptions() {
        return new Options()
          .addOption(Option.builder("h")
            .longOpt("help")
            .desc("print help message")
            .build())
          .addOption(Option.builder("m")
            .longOpt("model")
            .desc("directory for the model file[s] (.smithy format). Also the Dafny output directory.")
            .hasArg()
            .required()
            .build())
          .addOption(Option.builder("d")
            .longOpt("dependent-model")
            .desc("directory for dependent the model file[s] (.smithy format)")
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
            .desc("output directory for generated .NET files")
            .hasArg()
            .required()
            .build())
          .addOption(Option.builder()
            .longOpt("output-java")
            .desc("output directory for generated Java files")
            .hasArg()
            .required()
            .build())
          .addOption(Option.builder()
            .longOpt("aws-sdk")
            .desc("generate AWS SDK-style API and shims")
            .build());
    }

    private static void printHelpMessage() {
        new HelpFormatter().printHelp("smithy-polymorph", getCliOptions());
    }

    private record CliArguments(
            Path modelPath,
            Path[] dependentModelPaths,
            String namespace,
            Path outputDotnetDir,
            Path outputJavaDir, boolean awsSdkStyle
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
                return Optional.empty();
            }

            final Path modelPath = Path.of(commandLine.getOptionValue('m'));

            final Path[] dependentModelPaths = Arrays
              .stream(commandLine.getOptionValues('d'))
              .map(Path::of)
              .toArray(Path[]::new);

            final String namespace = commandLine.getOptionValue('n');
            final Path outputDotnetDir = Paths.get(commandLine.getOptionValue("output-dotnet"))
                    .toAbsolutePath().normalize();
            final Path outputJavaDir = Paths.get(commandLine.getOptionValue("output-java"))
                    .toAbsolutePath().normalize();
            final boolean awsSdkStyle = commandLine.hasOption("aws-sdk");

            return Optional.of(new CliArguments(
              modelPath, dependentModelPaths, namespace, outputDotnetDir, outputJavaDir, awsSdkStyle));
        }
    }

    private static void writeToFile(final String text, final File file) {
        try {
            if (!file.createNewFile()) {
                logger.warn("Overwriting existing file {}", file);
            }
            final FileWriter fileWriter = new FileWriter(file);
            fileWriter.write(text);
            if (!text.endsWith("\n")) {
                fileWriter.write("\n");
            }
            fileWriter.close();
        } catch (IOException e) {
            logger.error("Could not write to file {}", file);
            e.printStackTrace();
        }
    }

    private static final String COPYRIGHT_HEADER = """
            // Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
            // SPDX-License-Identifier: Apache-2.0
            """;

    public static final String GENERATED_HEADER = """
            // Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
            """;

    private static void writeTokenTreesIntoDir(final Map<Path, TokenTree> tokenTreeMap, final Path outputDir) {
        tokenTreeMap.forEach((Path localPath, TokenTree tokens) -> {
            final Path outputPath = Path.of(outputDir.toString(), localPath.toString());
            final String content = COPYRIGHT_HEADER + GENERATED_HEADER + tokens.toString();
            writeToFile(content, outputPath.toFile());
        });
    }
}
