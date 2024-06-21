package software.amazon.smithy.dafny.codegen;

import org.junit.jupiter.api.Assertions;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;
import software.amazon.polymorph.utils.IOUtils;
import software.amazon.smithy.utils.IoUtils;

import java.io.ByteArrayOutputStream;
import java.io.File;
import java.io.IOException;
import java.nio.file.Path;
import java.nio.file.Paths;
import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import static org.hamcrest.Matchers.containsString;
import static org.hamcrest.MatcherAssert.assertThat;

class CodegenCliTest {

    @ParameterizedTest
    @ValueSource(strings = {
            "SimpleTypes/SimpleString",
            "SimpleTypes/SimpleBoolean",
            "SimpleTypes/SimpleInteger",
            "SimpleTypes/SimpleLong",

    })
    void testModelsForDotnet(String relativeTestModelPath) {
        System.out.println("HELLO");
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
            "JAVA_HOME",
            "PATH",
            "DOTNET_CLI_HOME",
            "DAFNY_VERSION"
    };

    private static void make(Path workdir, String... makeArgs) {
        Map<String, String> env = Arrays.stream(PASSTHROUGH_ENVIRONMENT_VARIABLES)
                .collect(Collectors.toMap(name -> name, System::getenv));
        List<String> args = Stream.concat(Stream.of("make"), Stream.of(makeArgs)).toList();
        
        System.out.println("[[[" + args + "]]]");
        int exitCode = IoUtils.runCommand(args, workdir, System.out, env);
        if (exitCode != 0) {
            throw new RuntimeException("make command failed (exit code: " + exitCode + ")");
        }
    }
}