package software.amazon.smithy.dafny.codegen;

import static java.util.function.Function.identity;

import java.nio.file.Path;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import software.amazon.smithy.utils.IoUtils;

public class TestUtils {

  private static Set<String> passthroughEnvrionmentVariables() {
    return Set.of("PATH");
  }

  public static void make(Path workdir, String... makeArgs) {
    List<String> missingEnvVars = passthroughEnvrionmentVariables()
      .stream()
      .filter(name -> System.getenv(name) == null)
      .toList();
    if (!missingEnvVars.isEmpty()) {
      throw new IllegalStateException(
        "Missing required environment variables: " + missingEnvVars
      );
    }

    Map<String, String> env = passthroughEnvrionmentVariables()
      .stream()
      .collect(Collectors.toMap(identity(), System::getenv));
    List<String> args = Stream
      .concat(Stream.of("make"), Stream.of(makeArgs))
      .toList();

    StringBuffer output = new StringBuffer();
    int exitCode = IoUtils.runCommand(args, workdir, output, env);
    if (exitCode != 0) {
      throw new RuntimeException(
        "make command [" +
        args +
        "] failed (exit code: " +
        exitCode +
        "). Output:\n" +
        output
      );
    }
  }
}
