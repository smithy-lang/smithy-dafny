package software.amazon.polymorph.smithyrust.generator;

import java.util.Arrays;
import java.util.Set;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import software.amazon.polymorph.utils.TokenTree;

public class RustUtils {

  private static final Set<String> RESERVED_WORDS = Set.of(
    "Self",
    "abstract",
    "as",
    "async",
    "await",
    "become",
    "box",
    "break",
    "const",
    "continue",
    "crate",
    "do",
    "dyn",
    "else",
    "enum",
    "extern",
    "false",
    "final",
    "fn",
    "for",
    "if",
    "impl",
    "in",
    "let",
    "loop",
    "macro",
    "match",
    "mod",
    "move",
    "mut",
    "override",
    "priv",
    "pub",
    "ref",
    "return",
    "self",
    "static",
    "struct",
    "super",
    "trait",
    "true",
    "try",
    "type",
    "typeof",
    "unsafe",
    "unsized",
    "use",
    "virtual",
    "where",
    "while",
    "yield"
  );

  public static String escapedName(String s) {
    if (RESERVED_WORDS.contains(s)) {
      return "r#" + s;
    } else {
      return s;
    }
  }

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
