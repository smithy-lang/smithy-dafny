// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph;

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
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.shapes.ShapeId;

import java.io.File;
import java.io.FileWriter;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.time.LocalDateTime;
import java.time.format.DateTimeFormatter;
import java.util.Map;
import java.util.Optional;

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
        final Path outputDafnyDir = cliArguments.outputDafnyDir;
        try {
            Files.createDirectories(outputDotnetDir);
            Files.createDirectories(outputDafnyDir);
        } catch (IOException e) {
            e.printStackTrace();
            System.exit(1);
        }

        final ModelAssembler assembler = new ModelAssembler();
        final Model model = assembler.addImport(cliArguments.modelPath).assemble().unwrap();

        if (!cliArguments.awsSdkStyle) {
            final ServiceCodegen serviceCodegen = new ServiceCodegen(model, cliArguments.serviceShapeId);
            writeTokenTreesIntoDir(serviceCodegen.generate(), outputDotnetDir);

            final ShimCodegen shimCodegen = new ShimCodegen(model, cliArguments.serviceShapeId);
            writeTokenTreesIntoDir(shimCodegen.generate(), outputDotnetDir);
        }

        final TypeConversionCodegen typeConversionCodegen = cliArguments.awsSdkStyle
                ? new AwsSdkTypeConversionCodegen(model, cliArguments.serviceShapeId)
                : new TypeConversionCodegen(model, cliArguments.serviceShapeId);
        writeTokenTreesIntoDir(typeConversionCodegen.generate(), outputDotnetDir);

        if (cliArguments.awsSdkStyle) {
            // TODO generate Dafny API for regular models too
            final DafnyApiCodegen dafnyApiCodegen = new DafnyApiCodegen(model, cliArguments.serviceShapeId);
            writeTokenTreesIntoDir(dafnyApiCodegen.generate(), outputDafnyDir);

            final AwsSdkShimCodegen shimCodegen = new AwsSdkShimCodegen(model, cliArguments.serviceShapeId);
            writeTokenTreesIntoDir(shimCodegen.generate(), outputDotnetDir);
        }

        logger.info(".NET code generated in {}", cliArguments.outputDotnetDir);
        logger.info("Dafny code generated in {}", cliArguments.outputDafnyDir);
    }

    private static Options getCliOptions() {
        final Options cliOptions = new Options();
        cliOptions.addOption(Option.builder("h")
                .longOpt("help")
                .desc("print help message")
                .build());
        cliOptions.addOption(Option.builder("m")
                .longOpt("model")
                .desc("model file (.smithy format)")
                .hasArg()
                .required()
                .build());
        cliOptions.addOption(Option.builder("s")
                .longOpt("service-id")
                .desc("service ID to generate code for, such as 'com.foo#BarService'")
                .hasArg()
                .required()
                .build());
        cliOptions.addOption(Option.builder()
                .longOpt("output-dotnet")
                .desc("output directory for generated .NET files")
                .hasArg()
                .required()
                .build());
        cliOptions.addOption(Option.builder()
                .longOpt("output-dafny")
                .desc("output directory for generated Dafny files")
                .hasArg()
                .required()
                .build());
        cliOptions.addOption(Option.builder()
                .longOpt("aws-sdk")
                .desc("generate AWS SDK-style API and shims")
                .build());
        return cliOptions;
    }

    private static void printHelpMessage() {
        new HelpFormatter().printHelp("smithy-dotnet", getCliOptions());
    }

    private static record CliArguments(
            Path modelPath,
            ShapeId serviceShapeId,
            Path outputDotnetDir,
            Path outputDafnyDir,
            boolean awsSdkStyle
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
            final ShapeId serviceShapeId = ShapeId.from(commandLine.getOptionValue('s'));
            final Path outputDotnetDir = Paths.get(commandLine.getOptionValue("output-dotnet"))
                    .toAbsolutePath().normalize();
            final Path outputDafnyDir = Paths.get(commandLine.getOptionValue("output-dafny"))
                    .toAbsolutePath().normalize();
            final boolean awsSdkStyle = commandLine.hasOption("aws-sdk");

            return Optional.of(new CliArguments(
                    modelPath, serviceShapeId, outputDotnetDir, outputDafnyDir, awsSdkStyle));
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

    private static void writeTokenTreesIntoDir(final Map<Path, TokenTree> tokenTreeMap, final Path outputDir) {
        tokenTreeMap.forEach((Path localPath, TokenTree tokens) -> {
            final Path outputPath = Path.of(outputDir.toString(), localPath.toString());
            writeToFile(COPYRIGHT_HEADER + tokens.toString(), outputPath.toFile());
        });
    }
}
