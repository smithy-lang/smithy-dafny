package software.amazon.polymorph.smithyrust.generator;

import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toSnakeCase;

import java.util.Arrays;
import java.util.stream.Collectors;

public class NamespaceHelper {

  public static String rustModuleForSmithyNamespace(
    final String smithyNamespace
  ) {
    return Arrays
      .stream(smithyNamespace.split("\\."))
      .collect(Collectors.joining("_"));
  }
}
