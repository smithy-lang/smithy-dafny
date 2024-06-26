package software.amazon.smithy.dafny.codegen;

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
import java.util.List;
import java.util.Map;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static java.util.function.Function.identity;

class CodegenCliTest {

    private static final Logger LOGGER = LoggerFactory.getLogger(
            CodegenCliTest.class
    );

    private static class LoggerAppendable implements Appendable {

        private final Logger logger;

        private LoggerAppendable(Logger logger) {
            this.logger = logger;
        }

        @Override
        public Appendable append(CharSequence csq) throws IOException {
            logger.trace(null, () -> csq.toString());
            return this;
        }

        @Override
        public Appendable append(CharSequence csq, int start, int end) throws IOException {
            logger.trace(null, () -> csq.subSequence(start, end).toString());
            return this;
        }

        @Override
        public Appendable append(char c) throws IOException {
            throw new UnsupportedOperationException();
        }
    }

    private static Stream<String> discoverTestModels() throws IOException {
        var testModelRoot = Paths.get(".")
                .resolve("..")
                .resolve("..")
                .resolve("TestModels");
        return Files.walk(testModelRoot)
                    .filter(p -> Files.exists(p.resolve("Makefile")))
                    .map(testModelRoot::relativize)
                    .map(Path::toString);
    }

    @ParameterizedTest
    @MethodSource("discoverTestModels")
    void testModelsForDotnet(String relativeTestModelPath) {
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