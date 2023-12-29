// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice.extensions;

import static java.lang.String.format;

import java.util.logging.Logger;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.localservice.customize.ReferencesFileWriter;
import software.amazon.smithy.codegen.core.*;
import software.amazon.smithy.codegen.core.directed.*;
import software.amazon.smithy.python.codegen.*;

/**
 * DirectedCodegen for Dafny Python LocalServices. This overrides Smithy-Python's
 * DirectedPythonCodegen to not write symbols in a different namespace.
 */
public class DirectedDafnyPythonLocalServiceCodegen extends DirectedPythonCodegen {

  private static final Logger LOGGER =
      Logger.getLogger(DirectedDafnyPythonLocalServiceCodegen.class.getName());

  @Override
  public SymbolProvider createSymbolProvider(
      CreateSymbolProviderDirective<PythonSettings> directive) {
    return new DafnyPythonLocalServiceSymbolVisitor(directive.model(), directive.settings());
  }

  @Override
  public void customizeBeforeShapeGeneration(
      CustomizeDirective<GenerationContext, PythonSettings> directive) {
    generateServiceErrors(directive.settings(), directive.context().writerDelegator());
    new DafnyPythonLocalServiceConfigGenerator(directive.settings(), directive.context()).run();
  }

  /**
   * Override Smithy-Python's generateServiceErrors to generate symbols in the correct directories.
   * @param settings
   * @param writers
   */
  @Override
  protected void generateServiceErrors(
      PythonSettings settings, WriterDelegator<PythonWriter> writers) {
    var serviceError =
        Symbol.builder()
            .name("ServiceError")
            .namespace(
                format(
                    "%s.errors",
                    SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
                        settings.getService().getNamespace(), settings)),
                ".")
            .definitionFile(
                format(
                    "./%s/errors.py",
                    SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
                        settings.getService().getNamespace())))
            .build();
    writers.useFileWriter(
        serviceError.getDefinitionFile(),
        serviceError.getNamespace(),
        writer -> {
          // TODO: subclass a shared error
          writer.openBlock(
              "class $L(Exception):",
              "",
              serviceError.getName(),
              () -> {
                writer.writeDocs("Base error for all errors in the service.");
                writer.write("pass");
              });
        });
    var apiError =
        Symbol.builder()
            .name("ApiError")
            .namespace(
                format(
                    "%s.errors",
                    SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
                        settings.getService().getNamespace(), settings)),
                ".")
            .definitionFile(
                format(
                    "./%s/errors.py",
                    SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
                        settings.getService().getNamespace())))
            .build();
    writers.useFileWriter(
        apiError.getDefinitionFile(),
        apiError.getNamespace(),
        writer -> {
          writer.addStdlibImport("typing", "Generic");
          writer.addStdlibImport("typing", "TypeVar");
          writer.write("T = TypeVar('T')");
          writer.openBlock(
              "class $L($T, Generic[T]):",
              "",
              apiError.getName(),
              serviceError,
              () -> {
                writer.writeDocs("Base error for all api errors in the service.");
                writer.write("code: T");
                writer.openBlock(
                    "def __init__(self, message: str):",
                    "",
                    () -> {
                      writer.write("super().__init__(message)");
                      writer.write("self.message = message");
                    });
              });

          var unknownApiError =
              Symbol.builder()
                  .name("UnknownApiError")
                  .namespace(
                      format(
                          "%s.errors",
                          SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
                              settings.getService().getNamespace(), settings)),
                      ".")
                  .definitionFile(
                      format(
                          "./%s/errors.py",
                          SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
                              settings.getService().getNamespace())))
                  .build();
          writer.addStdlibImport("typing", "Literal");
          writer.openBlock(
              "class $L($T[Literal['Unknown']]):",
              "",
              unknownApiError.getName(),
              apiError,
              () -> {
                writer.writeDocs("Error representing any unknown api errors");
                writer.write("code: Literal['Unknown'] = 'Unknown'");
              });
        });
  }

  /**
   * Override Smithy-Python's generateResource to actually generate resources.
   * @param directive Directive to perform.
   */
  @Override
  public void generateResource(
      GenerateResourceDirective<GenerationContext, PythonSettings> directive) {
    if (directive
        .shape()
        .getId()
        .getNamespace()
        .equals(directive.context().settings().getService().getNamespace())) {
      String moduleName =
          SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
              directive.context().settings().getService().getNamespace());
      directive
          .context()
          .writerDelegator()
          .useFileWriter(
              moduleName + "/references.py",
              "",
              writer -> {
                new ReferencesFileWriter()
                    .generateResourceInterface(directive.shape(), directive.context(), writer);
              });
    }
  }

  /**
   * Override Smithy-Python's generateStructure to not write a symbol in a different namespace.
   * @param directive Directive to perform.
   */
  @Override
  public void generateStructure(
      GenerateStructureDirective<GenerationContext, PythonSettings> directive) {
    if (directive
        .shape()
        .getId()
        .getNamespace()
        .equals(directive.context().settings().getService().getNamespace())) {

      directive
          .context()
          .writerDelegator()
          .useShapeWriter(
              directive.shape(),
              writer -> {
                DafnyPythonLocalServiceStructureGenerator generator =
                    new DafnyPythonLocalServiceStructureGenerator(
                        directive.model(),
                        directive.settings(),
                        directive.symbolProvider(),
                        writer,
                        directive.shape(),
                        TopologicalIndex.of(directive.model()).getRecursiveShapes());
                generator.run();
              });
    }
  }

  /**
   * Override Smithy-Python's generateError to not write a symbol in a different namespace.
   * @param directive Directive to perform.
   */
  @Override
  public void generateError(GenerateErrorDirective<GenerationContext, PythonSettings> directive) {
    if (directive
        .shape()
        .getId()
        .getNamespace()
        .equals(directive.context().settings().getService().getNamespace())) {

      directive
          .context()
          .writerDelegator()
          .useShapeWriter(
              directive.shape(),
              writer -> {
                DafnyPythonLocalServiceStructureGenerator generator =
                    new DafnyPythonLocalServiceStructureGenerator(
                        directive.model(),
                        directive.settings(),
                        directive.symbolProvider(),
                        writer,
                        directive.shape(),
                        TopologicalIndex.of(directive.model()).getRecursiveShapes());
                generator.run();
              });
    }
  }

  /**
   * Override Smithy-Python's generateUnion to not write a symbol in a different namespace.
   * @param directive Directive to perform.
   */
  @Override
  public void generateUnion(GenerateUnionDirective<GenerationContext, PythonSettings> directive) {
    if (directive
        .shape()
        .getId()
        .getNamespace()
        .equals(directive.context().settings().getService().getNamespace())) {

      directive
          .context()
          .writerDelegator()
          .useShapeWriter(
              directive.shape(),
              writer -> {
                UnionGenerator generator =
                    new UnionGenerator(
                        directive.model(),
                        directive.symbolProvider(),
                        writer,
                        directive.shape(),
                        TopologicalIndex.of(directive.model()).getRecursiveShapes());
                generator.run();
              });
    }
  }

    /**
     * Override Smithy-Python's generateService to generate a synchronous client.
     * @param directive Directive to perform.
     */
  @Override
  public void generateService(
      GenerateServiceDirective<GenerationContext, PythonSettings> directive) {
    new SynchronousClientGenerator(directive.context(), directive.service()).run();

    var protocolGenerator = directive.context().protocolGenerator();
    if (protocolGenerator == null) {
      return;
    }

    protocolGenerator.generateSharedSerializerComponents(directive.context());
    protocolGenerator.generateRequestSerializers(directive.context());

    protocolGenerator.generateSharedDeserializerComponents(directive.context());
    protocolGenerator.generateResponseDeserializers(directive.context());

    protocolGenerator.generateProtocolTests(directive.context());
  }

}
