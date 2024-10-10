package software.amazon.polymorph.smithyrust.generator;

import java.util.Arrays;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import software.amazon.polymorph.utils.TokenTree;

public class RustUtils {

  public static String rustModuleForSmithyNamespace(
    final String smithyNamespace
  ) {
    return Arrays
      .stream(smithyNamespace.split("\\."))
      .collect(Collectors.joining("_"));
  }

  public static TokenTree declarePubModules(Stream<String> moduleNames) {
    return TokenTree
      .of(
        moduleNames
          .sorted()
          .map(module -> TokenTree.of("pub mod " + module + ";\n"))
      )
      .lineSeparated();
  }
}
