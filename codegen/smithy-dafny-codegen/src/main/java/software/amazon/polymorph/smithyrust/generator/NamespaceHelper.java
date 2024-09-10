package software.amazon.polymorph.smithyrust.generator;

import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toSnakeCase;

public class NamespaceHelper {

  /**
   * TODO: This is only hypothetical and untested at present,
   * because smithy-dafny doesn't yet support building multiple Smithy models
   * into either separate related crates or a single merged crate.
   */
  public static String rustModuleForSmithyNamespace(
    final String smithyNamespace
  ) {
    final String[] components = smithyNamespace.split("\\.");
    final String lastComponent = components[components.length - 1];
    return toSnakeCase(lastComponent);
  }
}
