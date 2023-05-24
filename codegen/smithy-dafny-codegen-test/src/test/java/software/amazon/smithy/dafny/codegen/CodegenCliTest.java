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

// I'd love to replace the GitHub workflows that are testing all TestModels with this approach,
// but although it's straightforward to model them with a @ParameterizedTest,
// I haven't yet worked out how to execute them in parallel,
// and without that we'll have a fairly significant CI efficiency regression.
// For now, we can at least use this harness for negative tests of unsupported models.
class CodegenCliTest {

    @Test
    public void testUnsupportedShape() {
        Path testModelPath = getTestModelPath("SimpleTypes/SimpleDocument");
        AssertionError e = Assertions.assertThrows(AssertionError.class, () ->
                make(testModelPath, "polymorph_dafny"));
        String expectedMessage = "Exception in thread \"main\" java.lang.IllegalArgumentException: The following shapes in the service's closure are not supported: \n" +
                "(document: `smithy.api#Document`)\n" +
                " - (shape type `document` is not supported)";
        assertThat(e.getMessage(), containsString(expectedMessage));
    }

    @Test
    public void testUnsupportedTrait() {
        Path testModelPath = getTestModelPath("Streaming");
        AssertionError e = Assertions.assertThrows(AssertionError.class, () ->
                make(testModelPath, "polymorph_dafny"));
        String expectedMessage = "Exception in thread \"main\" java.lang.IllegalArgumentException: The following shapes in the service's closure are not supported: \n" +
                "(document: `smithy.api#Document`)\n" +
                " - (shape type `document` is not supported)";
        assertThat(e.getMessage(), containsString(expectedMessage));
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
            "DOTNET_CLI_HOME"
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