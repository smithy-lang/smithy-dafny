package software.amazon.smithy.dafny.codegen;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.hamcrest.Matchers.containsString;
import static org.hamcrest.MatcherAssert.assertThat;

class CodegenCliTest {

    @ParameterizedTest
    @ValueSource(strings = {
            "SimpleTypes/SimpleString"
    })
    void testModelsForJava(String relativeTestModelPath) {
        Path testModelPath = getTestModelPath(relativeTestModelPath);
        make(testModelPath, "polymorph_dafny");
        make(testModelPath, "polymorph_java");
        make(testModelPath, "build_java");
        make(testModelPath, "test_java");
    }

    private Path getTestModelPath(String relativeTestModelPath) {
        return Paths.get(".")
                .resolve("..")
                .resolve("..")
                .resolve("TestModels")
                .resolve(relativeTestModelPath);
    }

    private static final String[] PASSTHROUGH_ENVIRONMENT_VARIABLES = new String[] {
            "JAVA_HOME",
            "PATH",
            "DOTNET_CLI_HOME",
            "DAFNY_VERSION"
    };

    private static void make(Path workdir, String... makeArgs) {
        String[] envp = Arrays.stream(PASSTHROUGH_ENVIRONMENT_VARIABLES)
                .map(name -> name + "=" + System.getenv(name))
                .toArray(String[]::new);
        String[] args = Stream.concat(Stream.of("make"), Stream.of(makeArgs)).toArray(String[]::new);
        RunCommand(workdir.toFile(), envp, args);
    }

    private static void RunCommand(File workdir, String[] envp, String[] args) {
        try {
            Runtime rt = Runtime.getRuntime();
            Process pr = rt.exec(args, envp, workdir);
            int exitCode = pr.waitFor();

            ByteArrayOutputStream outBaos = new ByteArrayOutputStream();
            pr.getInputStream().transferTo(outBaos);
            String output = outBaos.toString();

            ByteArrayOutputStream errBaos = new ByteArrayOutputStream();
            pr.getErrorStream().transferTo(errBaos);
            String error = errBaos.toString();

            if (exitCode != 0) {
                throw new AssertionError("Command returned a non-zero error code: " + exitCode
                        + "\n" + output + "\n" + error);
            }
        } catch (IOException | InterruptedException e) {
            throw new RuntimeException(e);
        }
    }
}