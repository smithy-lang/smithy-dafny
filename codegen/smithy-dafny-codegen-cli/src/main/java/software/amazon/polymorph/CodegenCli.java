// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph;

import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.HelpFormatter;
import org.apache.commons.cli.Option;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;
import org.slf4j.Logger;
import org.slf4j.LoggerFactory;
import software.amazon.polymorph.CodegenEngine.TargetLanguage;
import software.amazon.polymorph.smithydafny.DafnyVersion;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject.AwsSdkVersion;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.validation.ValidatedResult;
import software.amazon.smithy.model.validation.ValidationEvent;

public class CodegenCli {

  private static final Logger LOGGER = LoggerFactory.getLogger(
    CodegenCli.class
  );

  private enum Command {
    GENERATE,
    PATCH_AFTER_TRANSPILE,
  }

  private static final Map<Command, Options> optionsForCommand = Map.of(
    Command.GENERATE,
    getCliOptionsForBuild(),
    Command.PATCH_AFTER_TRANSPILE,
    getCliOptionsForPatchAfterTranspile()
  );

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
      System.exit(1);
    }
    if (cliArgumentsOptional.isEmpty()) {
      printHelpMessage();
      System.exit(0);
    }
    final CliArguments cliArguments = cliArgumentsOptional.get();

    LOGGER.debug("Loading model from {}", cliArguments.modelPath);
    final ModelAssembler assembler = new ModelAssembler();
    assembler.addImport(cliArguments.modelPath);
    Arrays
      .stream(cliArguments.dependentModelPaths)
      .forEach(assembler::addImport);
    // Discover models from the classpath (e.g. models of library-defined traits)
    assembler.discoverModels();
    ValidatedResult<Model> result = assembler.assemble();
    final Model serviceModel = result.unwrap();
    // Validation succeeded but there may be events like WARNINGS, output them as well
    List<ValidationEvent> events = result.getValidationEvents();
    if (!events.isEmpty()) {
      LOGGER.warn(
        "Validation events:\n" +
        events
          .stream()
          .map(ValidationEvent::toString)
          .sorted()
          .collect(Collectors.joining("\n"))
      );
    }

    // If Smithy ever lets us configure this:
    // https://github.com/smithy-lang/smithy/blob/f598b87c51af5943686e38706847a5091fe718da/smithy-model/src/main/java/software/amazon/smithy/model/loader/ModelLoader.java#L76
    // We can remove this log statement.
    // (Alternatively, We could inline `addImport`,
    // and ignore dfy & md files. Link to `addImport` below)
    // https://github.com/smithy-lang/smithy/blob/f598b87c51af5943686e38706847a5091fe718da/smithy-model/src/main/java/software/amazon/smithy/model/loader/ModelAssembler.java#L256-L281
    LOGGER.info(
      "End annoying Smithy \"No ModelLoader was able to load\" warnings.\n\n"
    );

    final Map<TargetLanguage, Path> outputDirs = new HashMap<>();
    cliArguments.outputDafnyDir.ifPresent(path ->
      outputDirs.put(TargetLanguage.DAFNY, path)
    );
    cliArguments.outputJavaDir.ifPresent(path ->
      outputDirs.put(TargetLanguage.JAVA, path)
    );
    cliArguments.outputDotnetDir.ifPresent(path ->
      outputDirs.put(TargetLanguage.DOTNET, path)
    );
    cliArguments.outputRustDir.ifPresent(path ->
      outputDirs.put(TargetLanguage.RUST, path)
    );
    cliArguments.outputPythonDir.ifPresent(path ->
      outputDirs.put(TargetLanguage.PYTHON, path)
    );

    final Map<TargetLanguage, Path> testOutputDirs = new HashMap<>();
    cliArguments.testOutputJavaDir.ifPresent(path ->
      testOutputDirs.put(TargetLanguage.JAVA, path)
    );

    final CodegenEngine.Builder engineBuilder = new CodegenEngine.Builder()
      .withFromSmithyBuildPlugin(false)
      .withLibraryRoot(cliArguments.libraryRoot)
      .withServiceModel(serviceModel)
      .withDependentModelPaths(cliArguments.dependentModelPaths)
      .withDependencyLibraryNames(cliArguments.dependencyLibraryNames)
      .withNamespaces(cliArguments.namespaces)
      .withTargetLangOutputDirs(outputDirs)
      .withTargetLangTestOutputDirs(testOutputDirs)
      .withAwsSdkStyle(cliArguments.awsSdkStyle)
      .withDafnyVersion(cliArguments.dafnyVersion)
      .withUpdatePatchFiles(cliArguments.updatePatchFiles)
      .withGenerationAspects(cliArguments.generationAspects);
    // Rust currently generates all code for all dependencies at once,
    // and the makefile structure makes it very difficult to avoid passing --local-service-test
    // when we don't actually want it for --aws-sdk style projects.
    // For now just ignoring it with a warning.
    if (
      outputDirs.containsKey(TargetLanguage.RUST) &&
      cliArguments.awsSdkStyle &&
      cliArguments.localServiceTest
    ) {
      LOGGER.warn(
        "Ignoring --local-service-test because --output-rust and --aws-sdk are also present"
      );
    } else {
      engineBuilder.withLocalServiceTest(cliArguments.localServiceTest);
    }
    cliArguments.propertiesFile.ifPresent(engineBuilder::withPropertiesFile);
    cliArguments.javaAwsSdkVersion.ifPresent(
      engineBuilder::withJavaAwsSdkVersion
    );
    cliArguments.includeDafnyFile.ifPresent(
      engineBuilder::withIncludeDafnyFile
    );
    cliArguments.libraryName.ifPresent(engineBuilder::withLibraryName);
    cliArguments.patchFilesDir.ifPresent(engineBuilder::withPatchFilesDir);
    final CodegenEngine engine = engineBuilder.build();
    switch (cliArguments.command) {
      case GENERATE -> engine.run();
      case PATCH_AFTER_TRANSPILE -> engine.patchAfterTranspiling();
    }
  }

  private static Options getCliOptionsForBuild() {
    return new Options()
      .addOption(
        Option.builder("h").longOpt("help").desc("print help message").build()
      )
      .addOption(
        Option
          .builder("r")
          .longOpt("library-root")
          .desc("root directory of the library")
          .hasArg()
          .required()
          .build()
      )
      .addOption(
        Option
          .builder("m")
          .longOpt("model")
          .desc("directory for the model file[s] (.smithy or json format).")
          .hasArg()
          .required()
          .build()
      )
      .addOption(
        Option
          .builder("d")
          .longOpt("dependent-model")
          .desc("directory for dependent model file[s] (.smithy format)")
          .hasArg()
          .required()
          .build()
      )
      .addOption(
        Option
          .builder("dln")
          .longOpt("dependency-library-name")
          .desc(
            "namespace-to-library-name map entry for a dependency namespace"
          )
          .hasArg()
          .build()
      )
      .addOption(
        Option
          .builder("n")
          .longOpt("namespace")
          .desc("smithy namespace to generate code for, such as 'com.foo'")
          .hasArg()
          .valueSeparator(',')
          .build()
      )
      .addOption(
        Option
          .builder("ln")
          .longOpt("library-name")
          .desc(
            "if generating for a language that uses library names (go, python), the name of the library in that language"
          )
          .hasArg()
          .build()
      )
      .addOption(
        Option
          .builder()
          .longOpt("output-dotnet")
          .desc("<optional> output directory for generated .NET files")
          .hasArg()
          .build()
      )
      .addOption(
        Option
          .builder()
          .longOpt("output-java")
          .desc("<optional> output directory for generated Java files")
          .hasArg()
          .build()
      )
      .addOption(
        Option
          .builder()
          .longOpt("output-java-test")
          .desc("<optional> output directory for generated Java test files")
          .hasArg()
          .build()
      )
      .addOption(
        Option
          .builder()
          .longOpt("output-rust")
          .desc("<optional> output directory for generated Rust files")
          .hasArg()
          .build()
      )
      .addOption(
        Option
          .builder()
          .longOpt("output-python")
          .desc("<optional> output directory for generated Python files")
          .hasArg()
          .build()
      )
      .addOption(
        Option
          .builder()
          .longOpt("java-aws-sdk-version")
          .desc(
            "<optional> AWS SDK for Java version to use: v1, or v2 (default)"
          )
          .hasArg()
          .build()
      )
      .addOption(
        Option
          .builder()
          .longOpt("dafny-version")
          .desc("Dafny version to generate code for")
          .hasArg()
          .build()
      )
      .addOption(
        Option
          .builder()
          .longOpt("properties-file")
          .desc("Path to generate the project.properties file at")
          .hasArg()
          .build()
      )
      .addOption(
        Option
          .builder()
          .longOpt("aws-sdk")
          .desc("<optional> generate AWS SDK-style API and shims")
          .build()
      )
      .addOption(
        Option
          .builder()
          .longOpt("local-service-test")
          .desc("<optional> generate Dafny that tests a local service")
          .build()
      )
      .addOption(
        Option
          .builder()
          .longOpt("output-dafny")
          .desc("<optional> output directory for generated Dafny code")
          .hasArg()
          .optionalArg(true)
          .build()
      )
      .addOption(
        Option
          .builder()
          .longOpt("include-dafny")
          .desc("<optional> files to be include in the generated Dafny")
          .hasArg()
          .build()
      )
      .addOption(
        Option
          .builder()
          .longOpt("patch-files-dir")
          .desc(
            "<optional> location of patch files. Defaults to <library-root>/codegen-patches"
          )
          .hasArg()
          .build()
      )
      .addOption(
        Option
          .builder()
          .longOpt("update-patch-files")
          .desc(
            "<optional> update patch files in <patch-files-dir> instead of applying them"
          )
          .build()
      )
      .addOption(
        Option
          .builder()
          .longOpt("generate")
          .desc(
            "<optional> optional aspects to generate. Available aspects:\n" +
            CodegenEngine.GenerationAspect.helpText()
          )
          .hasArgs()
          .valueSeparator(',')
          .build()
      );
  }

  private static Options getCliOptionsForPatchAfterTranspile() {
    return new Options()
      .addOption(
        Option.builder("h").longOpt("help").desc("print help message").build()
      )
      .addOption(
        Option
          .builder("r")
          .longOpt("library-root")
          .desc("root directory of the library")
          .hasArg()
          .required()
          .build()
      )
      .addOption(
        Option
          .builder("m")
          .longOpt("model")
          .desc("directory for the model file[s] (.smithy or json format).")
          .hasArg()
          .required()
          .build()
      )
      .addOption(
        Option
          .builder("d")
          .longOpt("dependent-model")
          .desc("directory for dependent model file[s] (.smithy format)")
          .hasArg()
          .required()
          .build()
      )
      .addOption(
        Option
          .builder("n")
          .longOpt("namespace")
          .desc("smithy namespace to generate code for, such as 'com.foo'")
          .hasArg()
          .required()
          .build()
      )
      .addOption(
        Option
          .builder()
          .longOpt("output-rust")
          .desc("<optional> output directory for generated Rust files")
          .hasArg()
          .build()
      )
      .addOption(
        Option
          .builder()
          .longOpt("dafny-version")
          .desc("Dafny version that generated the code to patch")
          .hasArg()
          .build()
      )
      .addOption(
        Option
          .builder()
          .longOpt("aws-sdk")
          .desc(
            "<optional> patch Dafny generated code for AWS SDK-style API and shims"
          )
          .build()
      )
      .addOption(
        Option
          .builder()
          .longOpt("generate")
          .desc(
            "<optional> optional aspects to generate. Available aspects:\n" +
            CodegenEngine.GenerationAspect.helpText()
          )
          .hasArgs()
          .valueSeparator(',')
          .build()
      )
      .addOption(
        Option
          .builder()
          .longOpt("local-service-test")
          .desc("<optional> generate Dafny that tests a local service")
          .build()
      );
  }

  private static void printHelpMessage() {
    new HelpFormatter()
      .printHelp(
        "smithy-dafny-codegen-cli [generate]",
        getCliOptionsForBuild()
      );
    new HelpFormatter()
      .printHelp(
        "smithy-dafny-codegen-cli patch-after-transpile",
        getCliOptionsForPatchAfterTranspile()
      );
  }

  private record CliArguments(
    Command command,
    Path libraryRoot,
    Path modelPath,
    Path[] dependentModelPaths,
    Map<String, String> dependencyLibraryNames,
    Set<String> namespaces,
    Optional<String> libraryName,
    Optional<Path> outputDotnetDir,
    Optional<Path> outputJavaDir,
    Optional<Path> testOutputJavaDir,
    Optional<Path> outputRustDir,
    Optional<Path> outputPythonDir,
    Optional<Path> outputDafnyDir,
    Optional<AwsSdkVersion> javaAwsSdkVersion,
    DafnyVersion dafnyVersion,
    Optional<Path> propertiesFile,
    Optional<Path> includeDafnyFile,
    boolean awsSdkStyle,
    boolean localServiceTest,
    Optional<Path> patchFilesDir,
    boolean updatePatchFiles,
    Set<CodegenEngine.GenerationAspect> generationAspects
  ) {
    /**
     * @param args arguments to parse
     * @return parsed arguments, or {@code Optional.empty()} if help should be printed
     * @throws ParseException if command line arguments are invalid
     */
    static Optional<CliArguments> parse(String[] args) throws ParseException {
      final DefaultParser parser = new DefaultParser();
      final String commandString = args.length > 0 && !args[0].startsWith("-")
        ? args[0]
        : "generate";
      Command command = null;
      try {
        command =
          Command.valueOf(commandString.toUpperCase().replace("-", "_"));
      } catch (IllegalArgumentException e) {
        LOGGER.error("Unrecognized command: {}", commandString);
        printHelpMessage();
        System.exit(-1);
      }

      final Options options = optionsForCommand.get(command);
      if (options == null) {
        LOGGER.error("Unrecognized command: {}", command);
        printHelpMessage();
        System.exit(-1);
      }

      final CommandLine commandLine = parser.parse(options, args);
      if (commandLine.hasOption("h")) {
        printHelpMessage();
        return Optional.empty();
      }

      Path libraryRoot = Paths.get(commandLine.getOptionValue("library-root"));

      final Path modelPath = Path.of(commandLine.getOptionValue('m'));

      final Path[] dependentModelPaths = Arrays
        .stream(commandLine.getOptionValues('d'))
        .map(Path::of)
        .toArray(Path[]::new);

      // Maps a Smithy namespace to its module name
      // ex. `dependency-library-name=aws.cryptography.materialproviders=aws_cryptographic_materialproviders`
      // maps the Smithy namespace `aws.cryptography.materialproviders` to a module name `aws_cryptographic_materialproviders`
      // via a map key of "aws.cryptography.materialproviders" and a value of "aws_cryptographic_materialproviders"
      final Map<String, String> dependencyNamespacesToLibraryNamesMap =
        commandLine.hasOption("dependency-library-name")
          ? Arrays
            .stream(commandLine.getOptionValues("dln"))
            .map(s -> s.split("="))
            .collect(Collectors.toMap(i -> i[0], i -> i[1]))
          : new HashMap<>();

      final Set<String> namespaces = Optional
        .ofNullable(commandLine.getOptionValues("namespace"))
        .<Set<String>>map(ns -> new HashSet<>(Arrays.asList(ns)))
        .orElse(Collections.emptySet());

      final Optional<String> libraryName = Optional.ofNullable(
        commandLine.getOptionValue("library-name")
      );

      Optional<Path> outputDafnyDir = Optional
        .ofNullable(commandLine.getOptionValue("output-dafny"))
        .map(Paths::get);
      if (commandLine.hasOption("output-dafny") && outputDafnyDir.isEmpty()) {
        LOGGER.warn(
          "Using `output-dafny` without providing a Path argument is deprecated and will be removed."
        );
        LOGGER.warn("Assuming Dafny should be written to Model path.");
        outputDafnyDir =
          Optional.of(Paths.get(commandLine.getOptionValue("m")));
      }

      final Optional<Path> outputJavaDir = Optional
        .ofNullable(commandLine.getOptionValue("output-java"))
        .map(Paths::get);
      final Optional<Path> testOutputJavaDir = Optional
        .ofNullable(commandLine.getOptionValue("output-java-test"))
        .map(Paths::get);
      final Optional<Path> outputDotnetDir = Optional
        .ofNullable(commandLine.getOptionValue("output-dotnet"))
        .map(Paths::get);
      final Optional<Path> outputRustDir = Optional
        .ofNullable(commandLine.getOptionValue("output-rust"))
        .map(Paths::get);
      final Optional<Path> outputPythonDir = Optional
        .ofNullable(commandLine.getOptionValue("output-python"))
        .map(Paths::get);

      boolean localServiceTest = commandLine.hasOption("local-service-test");
      final boolean awsSdkStyle = commandLine.hasOption("aws-sdk");

      Optional<AwsSdkVersion> javaAwsSdkVersion = Optional.empty();
      if (commandLine.hasOption("java-aws-sdk-version")) {
        final String versionStr = commandLine
          .getOptionValue("java-aws-sdk-version")
          .trim()
          .toUpperCase();
        try {
          javaAwsSdkVersion = Optional.of(AwsSdkVersion.valueOf(versionStr));
        } catch (IllegalArgumentException ex) {
          LOGGER.error("Unknown Java AWS SDK version {}", versionStr);
          throw ex;
        }
      }

      DafnyVersion dafnyVersion = null;
      String versionStr = commandLine.getOptionValue("dafny-version");
      if (versionStr != null) {
        try {
          dafnyVersion = DafnyVersion.parse(versionStr.trim());
        } catch (IllegalArgumentException ex) {
          LOGGER.error("Could not parse --dafny-version: {}", versionStr);
          throw ex;
        }
      }

      Optional<Path> propertiesFile = Optional
        .ofNullable(commandLine.getOptionValue("properties-file"))
        .map(Paths::get);

      Optional<Path> includeDafnyFile = Optional
        .ofNullable(commandLine.getOptionValue("include-dafny"))
        .map(Paths::get);

      Optional<Path> patchFilesDir = Optional
        .ofNullable(commandLine.getOptionValue("patch-files-dir"))
        .map(Paths::get);
      final boolean updatePatchFiles = commandLine.hasOption(
        "update-patch-files"
      );

      final String[] generationAspectOptions = Optional
        .ofNullable(commandLine.getOptionValues("generate"))
        .orElse(new String[0]);
      final Set<CodegenEngine.GenerationAspect> generationAspects = Arrays
        .stream(generationAspectOptions)
        .map(CodegenEngine.GenerationAspect::fromOption)
        .collect(Collectors.toSet());

      return Optional.of(
        new CliArguments(
          command,
          libraryRoot,
          modelPath,
          dependentModelPaths,
          dependencyNamespacesToLibraryNamesMap,
          namespaces,
          libraryName,
          outputDotnetDir,
          outputJavaDir,
          testOutputJavaDir,
          outputRustDir,
          outputPythonDir,
          outputDafnyDir,
          javaAwsSdkVersion,
          dafnyVersion,
          propertiesFile,
          includeDafnyFile,
          awsSdkStyle,
          localServiceTest,
          patchFilesDir,
          updatePatchFiles,
          generationAspects
        )
      );
    }
  }
}
