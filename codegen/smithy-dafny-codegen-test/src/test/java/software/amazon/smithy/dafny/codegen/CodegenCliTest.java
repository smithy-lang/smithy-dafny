package software.amazon.smithy.dafny.codegen;

import org.junit.jupiter.api.Assumptions;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.MethodSource;
import org.junit.jupiter.params.provider.ValueSource;
import org.junit.platform.commons.logging.Logger;
import org.junit.platform.commons.logging.LoggerFactory;
import software.amazon.smithy.utils.IoUtils;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.IntStream;
import java.util.stream.Stream;

import static java.util.function.Function.identity;

class CodegenCliTest {

    // TODO: # One-off until TestModels migrate to 4.4.0
    //          - library: TestModels/LanguageSpecificLogic

    private static final Set<String> DISABLED_TESTS = new HashSet<>();
    static {
        DISABLED_TESTS.add("AggregateReferences");
        DISABLED_TESTS.add("LanguageSpecificLogic");
        DISABLED_TESTS.add("LocalService");
        DISABLED_TESTS.add("SimpleTypes/BigDecimal");
        DISABLED_TESTS.add("SimpleTypes/BigInteger");
        DISABLED_TESTS.add("SimpleTypes/SimpleByte");
        DISABLED_TESTS.add("SimpleTypes/SimpleFloat");
        DISABLED_TESTS.add("SimpleTypes/SimpleShort");
    }

    private static Stream<String> discoverTestModels() throws IOException {
        var testModelRoot = Paths.get(".")
                .resolve("..")
                .resolve("..")
                .resolve("TestModels");
        var allTestModels = Files.walk(testModelRoot)
                    .filter(p -> Files.exists(p.resolve("Makefile")))
                    .map(testModelRoot::relativize)
                    .map(Path::toString);
        return selectShard(allTestModels);
    }

    private static Stream<String> selectShard(Stream<String> list) {
        var sorted = list.sorted().toList();

        // Select the requested fraction of the test collections if using the JUNIT_SHARD[_COUNT] environment variables.
        var shardEnvVar = System.getenv("JUNIT_SHARD");
        var numShardsEnvVar = System.getenv("JUNIT_SHARD_COUNT");
        if (shardEnvVar != null || numShardsEnvVar != null) {
            if (shardEnvVar == null || numShardsEnvVar == null) {
                throw new IllegalArgumentException(
                        "The JUNIT_SHARD and JUNIT_SHARD_COUNT environment variables must both be provided.");
            }

            var shard = Integer.parseInt(shardEnvVar);
            var numShards = Integer.parseInt(numShardsEnvVar);
            if (numShards <= 0) {
                throw new IllegalArgumentException(
                        "JUNIT_SHARD_COUNT must be greater than 0.");
            }
            if (shard <= 0 || shard > numShards) {
                throw new IllegalArgumentException(
                        "JUNIT_SHARD must be at least 1 and at most JUNIT_SHARD_COUNT.");
            }

            return IntStream.range(0, sorted.size())
                            .filter(index -> index % numShards == shard - 1)
                            .mapToObj(sorted::get);
        }

        return sorted.stream();
    }

    @ParameterizedTest
    @MethodSource("discoverTestModels")
    void testModelsForDotnet(String relativeTestModelPath) {
        Assumptions.assumeFalse(DISABLED_TESTS.contains(relativeTestModelPath));

        Path testModelPath = getTestModelPath(relativeTestModelPath);
        make(testModelPath, "polymorph_dafny");
        make(testModelPath, "polymorph_dotnet");
        make(testModelPath, "transpile_net");
        make(testModelPath, "test_net");
    }

    private Path getTestModelPath(String relativeTestModelPath) {
        return Paths.get(".")
                .resolve("..")
                .resolve("..")
                .resolve("TestModels")
                .resolve(relativeTestModelPath);
    }

    private static final String[] PASSTHROUGH_ENVIRONMENT_VARIABLES = new String[] {
            "PATH",
            "DAFNY_VERSION"
    };

    private static void make(Path workdir, String... makeArgs) {
        List<String> missingEnvVars = Arrays.stream(PASSTHROUGH_ENVIRONMENT_VARIABLES)
              .filter(name -> System.getenv(name) == null)
              .toList();
        if (!missingEnvVars.isEmpty()) {
            throw new IllegalStateException("Missing required environment variables: " + missingEnvVars);
        }

        Map<String, String> env = Arrays.stream(PASSTHROUGH_ENVIRONMENT_VARIABLES)
                .collect(Collectors.toMap(identity(), System::getenv));
        List<String> args = Stream.concat(Stream.of("make"), Stream.of(makeArgs)).toList();

        StringBuffer output = new StringBuffer();
        int exitCode = IoUtils.runCommand(args, workdir, output, env);
        if (exitCode != 0) {
            throw new RuntimeException("make command failed (exit code: " + exitCode + "). Output:\n" + output);
        }
    }
}