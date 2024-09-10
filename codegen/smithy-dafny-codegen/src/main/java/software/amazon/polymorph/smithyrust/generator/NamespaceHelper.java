package software.amazon.polymorph.smithyrust.generator;

import static software.amazon.smithy.rust.codegen.core.util.StringsKt.toSnakeCase;

public class NamespaceHelper {

  /**
   * TODO
   */
  public static String rustModuleForSmithyNamespace(final String smithyNamespace) {
    final String[] components = smithyNamespace.split(".");
    final String lastComponeent = components[components.length - 1];
    return toSnakeCase(lastComponeent);
  }
}
