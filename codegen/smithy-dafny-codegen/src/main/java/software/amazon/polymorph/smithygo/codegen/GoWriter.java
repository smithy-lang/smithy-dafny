package software.amazon.polymorph.smithygo.codegen;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.function.BiFunction;
import java.util.function.Consumer;
import java.util.function.Function;
import java.util.regex.Pattern;
import software.amazon.smithy.codegen.core.CodegenException;
import software.amazon.smithy.codegen.core.Symbol;
import software.amazon.smithy.codegen.core.SymbolContainer;
import software.amazon.smithy.codegen.core.SymbolDependency;
import software.amazon.smithy.codegen.core.SymbolReference;
import software.amazon.smithy.codegen.core.SymbolWriter;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.Prelude;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.traits.DeprecatedTrait;
import software.amazon.smithy.utils.StringUtils;

public class GoWriter extends SymbolWriter<GoWriter, ImportDeclarations> {

  private static final Pattern ARGUMENT_NAME_PATTERN = Pattern.compile(
    "\\$([a-z][a-zA-Z_0-9]+)(:\\w)?"
  );
  private final String fullPackageName;
  private final ImportDeclarations imports = new ImportDeclarations();
  private final List<SymbolDependency> dependencies = new ArrayList<>();
  private final boolean innerWriter;

  /**
   * Initializes the GoWriter for the package and filename to be written to.
   *
   * @param fullPackageName package and filename to be written to.
   */
  public GoWriter(String fullPackageName) {
    this(fullPackageName, false);
  }

  private GoWriter(String fullPackageName, boolean innerWriter) {
    super(new ImportDeclarations());
    this.fullPackageName = fullPackageName;
    this.innerWriter = innerWriter;
    init();
  }

  private void init() {
    trimBlankLines();
    trimTrailingSpaces();
    setIndentText("\t");
    putFormatter('T', new GoSymbolFormatter());
    putFormatter('P', new PointableGoSymbolFormatter());
    putFormatter('W', new GoWritableInjector());
  }

  // TODO figure out better way to annotate where the failure occurs, check templates and args
  // TODO to try to find programming bugs.

  /**
   * Returns a Writable for the string and args to be composed inline to another writer's contents.
   *
   * @param contents string to write.
   * @param args     Arguments to use when evaluating the contents string.
   * @return Writable to be evaluated.
   */
  @SafeVarargs
  public static Writable goTemplate(
    String contents,
    Map<String, Object>... args
  ) {
    validateTemplateArgsNotNull(args);
    return (GoWriter w) -> {
      w.writeGoTemplate(contents, args);
    };
  }

  public static final class GoWriterFactory
    implements SymbolWriter.Factory<GoWriter> {

    @Override
    public GoWriter apply(String filename, String namespace) {
      GoWriter writer = new GoWriter(namespace);
      return writer;
    }
  }

  /**
   * Returns a Writable that can later be invoked to write the contents as template
   * as a code block instead of single content of text.
   *
   * @param beforeNewLine text before new line
   * @param afterNewLine  text after new line
   * @param fn            closure to write
   */
  public static Writable goBlockTemplate(
    String beforeNewLine,
    String afterNewLine,
    Consumer<GoWriter> fn
  ) {
    return goBlockTemplate(beforeNewLine, afterNewLine, new Map[0], fn);
  }

  /**
   * Returns a Writable that can later be invoked to write the contents as template
   * as a code block instead of single content of text.
   *
   * @param beforeNewLine text before new line
   * @param afterNewLine  text after new line
   * @param args1         template arguments
   * @param fn            closure to write
   */
  public static Writable goBlockTemplate(
    String beforeNewLine,
    String afterNewLine,
    Map<String, Object> args1,
    Consumer<GoWriter> fn
  ) {
    return goBlockTemplate(
      beforeNewLine,
      afterNewLine,
      new Map[] { args1 },
      fn
    );
  }

  /**
   * Returns a Writable that can later be invoked to write the contents as template
   * as a code block instead of single content of text.
   *
   * @param beforeNewLine text before new line
   * @param afterNewLine  text after new line
   * @param args1         template arguments
   * @param args2         template arguments
   * @param fn            closure to write
   */
  public static Writable goBlockTemplate(
    String beforeNewLine,
    String afterNewLine,
    Map<String, Object> args1,
    Map<String, Object> args2,
    Consumer<GoWriter> fn
  ) {
    return goBlockTemplate(
      beforeNewLine,
      afterNewLine,
      new Map[] { args1, args2 },
      fn
    );
  }

  /**
   * Returns a Writable that can later be invoked to write the contents as template
   * as a code block instead of single content of text.
   *
   * @param beforeNewLine text before new line
   * @param afterNewLine  text after new line
   * @param args1         template arguments
   * @param args2         template arguments
   * @param args3         template arguments
   * @param fn            closure to write
   */
  public static Writable goBlockTemplate(
    String beforeNewLine,
    String afterNewLine,
    Map<String, Object> args1,
    Map<String, Object> args2,
    Map<String, Object> args3,
    Consumer<GoWriter> fn
  ) {
    return goBlockTemplate(
      beforeNewLine,
      afterNewLine,
      new Map[] { args1, args2, args3 },
      fn
    );
  }

  /**
   * Returns a Writable that can later be invoked to write the contents as template
   * as a code block instead of single content of text.
   *
   * @param beforeNewLine text before new line
   * @param afterNewLine  text after new line
   * @param args1         template arguments
   * @param args2         template arguments
   * @param args3         template arguments
   * @param args4         template arguments
   * @param fn            closure to write
   */
  public static Writable goBlockTemplate(
    String beforeNewLine,
    String afterNewLine,
    Map<String, Object> args1,
    Map<String, Object> args2,
    Map<String, Object> args3,
    Map<String, Object> args4,
    Consumer<GoWriter> fn
  ) {
    return goBlockTemplate(
      beforeNewLine,
      afterNewLine,
      new Map[] { args1, args2, args3, args4 },
      fn
    );
  }

  /**
   * Returns a Writable that can later be invoked to write the contents as template
   * as a code block instead of single content of text.
   *
   * @param beforeNewLine text before new line
   * @param afterNewLine  text after new line
   * @param args1         template arguments
   * @param args2         template arguments
   * @param args3         template arguments
   * @param args4         template arguments
   * @param args5         template arguments
   * @param fn            closure to write
   */
  public static Writable goBlockTemplate(
    String beforeNewLine,
    String afterNewLine,
    Map<String, Object> args1,
    Map<String, Object> args2,
    Map<String, Object> args3,
    Map<String, Object> args4,
    Map<String, Object> args5,
    Consumer<GoWriter> fn
  ) {
    return goBlockTemplate(
      beforeNewLine,
      afterNewLine,
      new Map[] { args1, args2, args3, args4, args5 },
      fn
    );
  }

  /**
   * Returns a Writable that can later be invoked to write the contents as template
   * as a code block instead of single content of text.
   *
   * @param beforeNewLine text before new line
   * @param afterNewLine  text after new line
   * @param args          template arguments
   * @param fn            closure to write
   */
  public static Writable goBlockTemplate(
    String beforeNewLine,
    String afterNewLine,
    Map<String, Object>[] args,
    Consumer<GoWriter> fn
  ) {
    validateTemplateArgsNotNull(args);
    return (GoWriter w) -> {
      w.writeGoBlockTemplate(beforeNewLine, afterNewLine, args, fn);
    };
  }

  /**
   * Returns a Writable that does nothing.
   *
   * @return Writable that does nothing
   */
  public static Writable emptyGoTemplate() {
    return (GoWriter w) -> {};
  }

  /**
   * Writes the contents and arguments as a template to the writer.
   *
   * @param contents string to write
   * @param args     Arguments to use when evaluating the contents string.
   */
  @SafeVarargs
  public final void writeGoTemplate(
    String contents,
    Map<String, Object>... args
  ) {
    withTemplate(
      contents,
      args,
      template -> {
        try {
          write(contents);
        } catch (Exception e) {
          throw new CodegenException(
            "Failed to render template\n" +
            contents +
            "\nReason: " +
            e.getMessage(),
            e
          );
        }
      }
    );
  }

  /**
   * Writes the contents as template as a code block instead of single content fo text.
   *
   * @param beforeNewLine text before new line
   * @param afterNewLine  text after new line
   * @param fn            closure to write
   */
  public void writeGoBlockTemplate(
    String beforeNewLine,
    String afterNewLine,
    Consumer<GoWriter> fn
  ) {
    writeGoBlockTemplate(beforeNewLine, afterNewLine, new Map[0], fn);
  }

  /**
   * Writes the contents as template as a code block instead of single content fo text.
   *
   * @param beforeNewLine text before new line
   * @param afterNewLine  text after new line
   * @param arg1          first map argument
   * @param fn            closure to write
   */
  public void writeGoBlockTemplate(
    String beforeNewLine,
    String afterNewLine,
    Map<String, Object> arg1,
    Consumer<GoWriter> fn
  ) {
    writeGoBlockTemplate(beforeNewLine, afterNewLine, new Map[] { arg1 }, fn);
  }

  /**
   * Writes the contents as template as a code block instead of single content fo text.
   *
   * @param beforeNewLine text before new line
   * @param afterNewLine  text after new line
   * @param arg1          first map argument
   * @param arg2          second map argument
   * @param fn            closure to write
   */
  public void writeGoBlockTemplate(
    String beforeNewLine,
    String afterNewLine,
    Map<String, Object> arg1,
    Map<String, Object> arg2,
    Consumer<GoWriter> fn
  ) {
    writeGoBlockTemplate(
      beforeNewLine,
      afterNewLine,
      new Map[] { arg1, arg2 },
      fn
    );
  }

  /**
   * Writes the contents as template as a code block instead of single content fo text.
   *
   * @param beforeNewLine text before new line
   * @param afterNewLine  text after new line
   * @param arg1          first map argument
   * @param arg2          second map argument
   * @param arg3          third map argument
   * @param fn            closure to write
   */
  public void writeGoBlockTemplate(
    String beforeNewLine,
    String afterNewLine,
    Map<String, Object> arg1,
    Map<String, Object> arg2,
    Map<String, Object> arg3,
    Consumer<GoWriter> fn
  ) {
    writeGoBlockTemplate(
      beforeNewLine,
      afterNewLine,
      new Map[] { arg1, arg2, arg3 },
      fn
    );
  }

  /**
   * Writes the contents as template as a code block instead of single content fo text.
   *
   * @param beforeNewLine text before new line
   * @param afterNewLine  text after new line
   * @param arg1          first map argument
   * @param arg2          second map argument
   * @param arg3          third map argument
   * @param arg4          forth map argument
   * @param fn            closure to write
   */
  public void writeGoBlockTemplate(
    String beforeNewLine,
    String afterNewLine,
    Map<String, Object> arg1,
    Map<String, Object> arg2,
    Map<String, Object> arg3,
    Map<String, Object> arg4,
    Consumer<GoWriter> fn
  ) {
    writeGoBlockTemplate(
      beforeNewLine,
      afterNewLine,
      new Map[] { arg1, arg2, arg3, arg4 },
      fn
    );
  }

  /**
   * Writes the contents as template as a code block instead of single content fo text.
   *
   * @param beforeNewLine text before new line
   * @param afterNewLine  text after new line
   * @param arg1          first map argument
   * @param arg2          second map argument
   * @param arg3          third map argument
   * @param arg4          forth map argument
   * @param arg5          forth map argument
   * @param fn            closure to write
   */
  public void writeGoBlockTemplate(
    String beforeNewLine,
    String afterNewLine,
    Map<String, Object> arg1,
    Map<String, Object> arg2,
    Map<String, Object> arg3,
    Map<String, Object> arg4,
    Map<String, Object> arg5,
    Consumer<GoWriter> fn
  ) {
    writeGoBlockTemplate(
      beforeNewLine,
      afterNewLine,
      new Map[] { arg1, arg2, arg3, arg4, arg5 },
      fn
    );
  }

  public void writeGoBlockTemplate(
    String beforeNewLine,
    String afterNewLine,
    Map<String, Object>[] args,
    Consumer<GoWriter> fn
  ) {
    withTemplate(
      beforeNewLine,
      args,
      header -> {
        conditionalBlock(header, afterNewLine, true, new Object[0], fn);
      }
    );
  }

  private void withTemplate(
    String template,
    Map<String, Object>[] argMaps,
    Consumer<String> fn
  ) {
    pushState();
    for (var args : argMaps) {
      putContext(args);
    }
    validateContext(template);
    fn.accept(template);
    popState();
  }

  private GoWriter conditionalBlock(
    String beforeNewLine,
    String afterNewLine,
    boolean conditional,
    Object[] args,
    Consumer<GoWriter> fn
  ) {
    if (conditional) {
      openBlock(beforeNewLine.trim(), args);
    }

    fn.accept(this);

    if (conditional) {
      closeBlock(afterNewLine.trim());
    }

    return this;
  }

  private static void validateTemplateArgsNotNull(
    Map<String, Object>[] argMaps
  ) {
    for (var args : argMaps) {
      args.forEach((k, v) -> {
        if (v == null) {
          throw new CodegenException(
            "Template argument " + k + " cannot be null"
          );
        }
      });
    }
  }

  private void validateContext(String template) {
    var matcher = ARGUMENT_NAME_PATTERN.matcher(template);

    while (matcher.find()) {
      var keyName = matcher.group(1);
      var value = getContext(keyName);
      if (value == null) {
        throw new CodegenException(
          "Go template expected " +
          keyName +
          " but was not present in context scope." +
          " Template: \n" +
          template
        );
      }
    }
  }

  /**
   * Imports one or more symbols if necessary, using the name of the
   * symbol and only "USE" references.
   *
   * @param container Container of symbols to add.
   * @return Returns the writer.
   */
  public GoWriter addUseImports(SymbolContainer container) {
    for (Symbol symbol : container.getSymbols()) {
      addImport(
        symbol,
        CodegenUtils.getSymbolNamespaceAlias(symbol),
        SymbolReference.ContextOption.USE
      );
    }
    return this;
  }

  /**
   * Imports a symbol reference if necessary, using the alias of the
   * reference and only associated "USE" references.
   *
   * @param symbolReference Symbol reference to import.
   * @return Returns the writer.
   */
  public GoWriter addUseImports(SymbolReference symbolReference) {
    return addImport(
      symbolReference.getSymbol(),
      symbolReference.getAlias(),
      SymbolReference.ContextOption.USE
    );
  }

  /**
   * Adds and imports the given dependency.
   *
   * @param goDependency The GoDependency to import.
   * @return Returns the writer.
   */
  public GoWriter addUseImports(GoDependency goDependency) {
    dependencies.addAll(goDependency.getDependencies());
    return addImport(goDependency.getImportPath(), goDependency.getAlias());
  }

  private GoWriter addImports(GoWriter other) {
    this.imports.addImports(other.imports);
    return this;
  }

  private boolean isExternalNamespace(String namespace) {
    return (
      !StringUtils.isBlank(namespace) && !namespace.equals(fullPackageName)
    );
  }

  void addImportReferences(
    Symbol symbol,
    SymbolReference.ContextOption... options
  ) {
    for (SymbolReference reference : symbol.getReferences()) {
      for (SymbolReference.ContextOption option : options) {
        if (reference.hasOption(option)) {
          addImport(reference.getSymbol(), reference.getAlias(), options);
          break;
        }
      }
    }
  }

  /**
   * Imports a package using an alias if necessary.
   *
   * @param packageName Package to import.
   * @param as          Alias to refer to the package as.
   * @return Returns the writer.
   */
  public GoWriter addImport(String packageName, String as) {
    imports.addImport(packageName, as);
    return this;
  }

  public GoWriter addImportFromModule(
    String moduleName,
    String packageName,
    String as
  ) {
    imports.addImport(moduleName.concat("/").concat(packageName), as);
    return this;
  }

  public GoWriter addImportFromModule(String moduleName, String packageName) {
    imports.addImport(moduleName.concat("/").concat(packageName), "");
    return this;
  }

  public GoWriter addImport(String packageName) {
    imports.addImport(packageName, "");
    return this;
  }

  private GoWriter addDependencies(GoWriter other) {
    this.dependencies.addAll(other.getDependencies());
    return this;
  }

  private boolean isTargetDeprecated(Model model, MemberShape member) {
    return (
      model
        .expectShape(member.getTarget())
        .getTrait(DeprecatedTrait.class)
        .isPresent() &&
      // don't consider deprecated prelude shapes (like PrimitiveBoolean)
      !Prelude.isPreludeShape(member.getTarget())
    );
  }

  @Override
  public String toString() {
    String contents = super.toString();

    if (innerWriter) {
      return contents;
    }

    String[] packageParts = fullPackageName.split("/");
    String header = String.format(
      "// Code generated by smithy-go-codegen DO NOT EDIT.%n%n"
    );

    String packageName = packageParts[packageParts.length - 1];
    if (packageName.startsWith("v") && packageParts.length >= 2) {
      String remaining = packageName.substring(1);
      try {
        int value = Integer.parseInt(remaining);
        packageName = packageParts[packageParts.length - 2];
        if (value == 0 || value == 1) {
          throw new CodegenException(
            "module paths vN version component must only be N >= 2"
          );
        }
      } catch (NumberFormatException ne) {
        // Do nothing
      }
    }

    String packageStatement = String.format("package %s%n%n", packageName);

    String importString = imports.toString();
    String strippedContents = StringUtils.stripStart(contents, null);
    String strippedImportString = StringUtils.strip(importString, null);

    // Don't add an additional new line between explicit imports and managed imports.
    if (
      !strippedImportString.isEmpty() && strippedContents.startsWith("import ")
    ) {
      return header + strippedImportString + "\n" + strippedContents;
    }

    return header + packageStatement + importString + contents;
  }

  /**
   * Implements Go symbol formatting for the {@code $T} formatter.
   */
  private class GoSymbolFormatter
    implements BiFunction<Object, String, String> {

    @Override
    public String apply(Object type, String indent) {
      if (type instanceof Symbol) {
        Symbol resolvedSymbol = (Symbol) type;
        // get symbol name for literal
        // Note: This literal could be changed in upcoming codes in this if block
        String literal = resolvedSymbol.getName();

        boolean isSlice = resolvedSymbol
          .getProperty(SymbolUtils.GO_SLICE, Boolean.class)
          .orElse(false);
        boolean isMap = resolvedSymbol
          .getProperty(SymbolUtils.GO_MAP, Boolean.class)
          .orElse(false);
        if (isSlice || isMap) {
          resolvedSymbol =
            resolvedSymbol
              .getProperty(SymbolUtils.GO_ELEMENT_TYPE, Symbol.class)
              .orElseThrow(() ->
                new CodegenException(
                  "Expected go element type property to be defined"
                )
              );
          literal =
            new PointableGoSymbolFormatter().apply(resolvedSymbol, "nested");
        } else if (
          !SymbolUtils.isUniverseType(resolvedSymbol) &&
          isExternalNamespace(resolvedSymbol.getNamespace())
        ) {
          // Change the literal to use namespace as well for symbol with external namespace
          literal = formatWithNamespace(resolvedSymbol);
        }
        addUseImports(resolvedSymbol);

        if (isSlice) {
          return "[]" + literal;
        } else if (isMap) {
          return "map[string]" + literal;
        } else {
          return literal;
        }
      } else if (type instanceof SymbolReference) {
        SymbolReference typeSymbol = (SymbolReference) type;
        addImport(
          typeSymbol.getSymbol(),
          typeSymbol.getAlias(),
          SymbolReference.ContextOption.USE
        );
        return typeSymbol.getAlias();
      } else {
        throw new CodegenException(
          "Invalid type provided to $T. Expected a Symbol, but found `" +
          type +
          "`"
        );
      }
    }

    private String formatWithNamespace(Symbol symbol) {
      if (StringUtils.isEmpty(symbol.getNamespace())) {
        return symbol.getName();
      }
      return String.format(
        "%s.%s",
        CodegenUtils.getSymbolNamespaceAlias(symbol),
        symbol.getName()
      );
    }
  }

  /**
   * Implements Go symbol formatting for the {@code $P} formatter. This is identical to the $T
   * formatter, except that it will add a * to symbols that can be pointers.
   */
  private class PointableGoSymbolFormatter extends GoSymbolFormatter {

    @Override
    public String apply(Object type, String indent) {
      String formatted = super.apply(type, indent);
      if (isPointer(type)) {
        formatted = "*" + formatted;
      }
      return formatted;
    }

    private boolean isPointer(Object type) {
      if (type instanceof Symbol) {
        Symbol typeSymbol = (Symbol) type;
        return typeSymbol
          .getProperty(SymbolUtils.POINTABLE, Boolean.class)
          .orElse(false);
      } else if (type instanceof SymbolReference) {
        SymbolReference typeSymbol = (SymbolReference) type;
        return (
          typeSymbol
            .getProperty(SymbolUtils.POINTABLE, Boolean.class)
            .orElse(false) ||
          typeSymbol
            .getSymbol()
            .getProperty(SymbolUtils.POINTABLE, Boolean.class)
            .orElse(false)
        );
      } else if (type instanceof String) {
        return true;
      } else {
        throw new CodegenException(
          "Invalid type provided to $P. Expected a Symbol, but found `" +
          type +
          "`"
        );
      }
    }
  }

  class GoWritableInjector extends GoSymbolFormatter {

    @Override
    public String apply(Object type, String indent) {
      if (!(type instanceof Writable)) {
        throw new CodegenException(
          "expect Writable for GoWriter W injector, but got " + type
        );
      }
      var innerWriter = new GoWriter(fullPackageName, true);
      ((Writable) type).accept(innerWriter);
      addImports(innerWriter);
      addDependencies(innerWriter);
      return innerWriter.toString().trim();
    }
  }

  public interface Writable extends Consumer<GoWriter> {}

  /**
   * Chains together multiple Writables that can be composed into one Writable.
   */
  public static final class ChainWritable {

    private final List<GoWriter.Writable> writables;

    public ChainWritable() {
      writables = new ArrayList<>();
    }

    public ChainWritable add(GoWriter.Writable writable) {
      writables.add(writable);
      return this;
    }

    public <T> ChainWritable add(Optional<T> value, Function<T, Writable> fn) {
      value.ifPresent(t -> writables.add(fn.apply(t)));
      return this;
    }

    public ChainWritable add(boolean include, GoWriter.Writable writable) {
      if (!include) {
        writables.add(writable);
      }
      return this;
    }

    public GoWriter.Writable compose() {
      return (GoWriter writer) -> {
        var hasPrevious = false;
        for (GoWriter.Writable writable : writables) {
          if (hasPrevious) {
            writer.write("");
          }
          hasPrevious = true;
          writer.write("$W", writable);
        }
      };
    }
  }
}
