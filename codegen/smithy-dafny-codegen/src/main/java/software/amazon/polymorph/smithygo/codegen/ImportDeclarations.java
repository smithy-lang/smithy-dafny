package software.amazon.polymorph.smithygo.codegen;

import java.util.Map;
import java.util.TreeMap;
import software.amazon.smithy.codegen.core.CodegenException;
import software.amazon.smithy.codegen.core.ImportContainer;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.utils.StringUtils;

public class ImportDeclarations implements ImportContainer {

  private final Map<String, String> imports = new TreeMap<>();

  ImportDeclarations addImport(String importPath, String alias) {
    String importAlias = CodegenUtils.getDefaultPackageImportName(importPath);
    if (!StringUtils.isBlank(alias)) {
      if (alias.equals(".")) {
        // Global imports are generally a bad practice.
        throw new CodegenException(
          "Globally importing packages is forbidden: " + importPath
        );
      }
      importAlias = alias;
    }
    imports.putIfAbsent(importAlias, importPath);
    return this;
  }

  ImportDeclarations addImports(ImportDeclarations other) {
    other.imports.forEach((importAlias, importPath) -> {
      addImport(importPath, importAlias);
    });
    return this;
  }

  @Override
  public String toString() {
    if (imports.isEmpty()) {
      return "";
    }

    StringBuilder builder = new StringBuilder("import (\n");
    for (Map.Entry<String, String> entry : imports.entrySet()) {
      builder.append('\t');
      builder.append(createImportStatement(entry));
      builder.append('\n');
    }
    builder.append(")\n\n");
    return builder.toString();
  }

  private String createImportStatement(Map.Entry<String, String> entry) {
    String formattedPackageName = "\"" + entry.getValue() + "\"";
    return CodegenUtils
        .getDefaultPackageImportName(entry.getValue())
        .equals(entry.getKey())
      ? formattedPackageName
      : entry.getKey() + " " + formattedPackageName;
  }

  @Override
  public void importSymbol(Symbol symbol, String alias) {
    addImport(symbol.getName(), alias);
  }
}
