// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.wrappedlocalservice.extensions;

import static java.lang.String.format;

import java.nio.file.Path;
import java.util.logging.Logger;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.localservice.extensions.DirectedDafnyPythonLocalServiceCodegen;
import software.amazon.polymorph.smithypython.wrappedlocalservice.WrappedCodegenConstants;
import software.amazon.smithy.build.FileManifest;
import software.amazon.smithy.codegen.core.CodegenException;
import software.amazon.smithy.codegen.core.SymbolProvider;
import software.amazon.smithy.codegen.core.directed.CreateSymbolProviderDirective;
import software.amazon.smithy.codegen.core.directed.CustomizeDirective;
import software.amazon.smithy.codegen.core.directed.GenerateResourceDirective;
import software.amazon.smithy.codegen.core.directed.GenerateServiceDirective;
import software.amazon.smithy.python.codegen.CodegenUtils;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonSettings;

/**
 * DirectedCodegen for Dafny Python wrapped LocalServices. This overrides DirectedPythonCodegen to
 * 1) Not generate a Smithy client (nor its serialize/deserialize bodies, client config, etc.)
 * 2) Remove extraneous generated files
 * Wrapped LocalService generation does NOT involve generating a Smithy client; it will only
 * generate a shim wrapping the LocalService-generated Smithy client.
 */
public class DirectedDafnyPythonWrappedLocalServiceCodegen
  extends DirectedDafnyPythonLocalServiceCodegen {

  private static final Logger LOGGER = Logger.getLogger(
    DirectedDafnyPythonWrappedLocalServiceCodegen.class.getName()
  );

  @Override
  public SymbolProvider createSymbolProvider(
    CreateSymbolProviderDirective<PythonSettings> directive
  ) {
    return new DafnyPythonWrappedLocalServiceSymbolVisitor(
      directive.model(),
      directive.settings()
    );
  }

  @Override
  public void generateResource(
    GenerateResourceDirective<GenerationContext, PythonSettings> directive
  ) {}

  /**
   * Do NOT generate any service config code for Dafny Python AWS SDKs (i.e. `config.py`). Override
   * DirectedPythonCodegen to block any service config code generation.
   *
   * @param directive Directive to perform.
   */
  @Override
  public void customizeBeforeShapeGeneration(
    CustomizeDirective<GenerationContext, PythonSettings> directive
  ) {}

  /**
   * Do NOT generate any service code for Dafny Python AWS SDKs. Override DirectedPythonCodegen to
   * block any service code generation. In addition to not writing any service code (i.e. not
   * writing `client.py`), this also blocks writing `serialize.py` and `deserialize.py`.
   *
   * @param directive Directive to perform.
   */
  @Override
  public void generateService(
    GenerateServiceDirective<GenerationContext, PythonSettings> directive
  ) {}

  /**
   * Call `DirectedPythonCodegen.customizeAfterIntegrations`, then remove `models.py` and
   * `errors.py`. The CodegenDirector will invoke this method after shape generation.
   *
   * @param directive Directive to perform.
   */
  @Override
  public void customizeAfterIntegrations(
    CustomizeDirective<GenerationContext, PythonSettings> directive
  ) {
    // DirectedPythonCodegen's customizeAfterIntegrations implementation SHOULD run first;
    //   its implementation writes all files by flushing its writers;
    //   this implementation removes some of those files.
    super.customizeAfterIntegrations(directive);

    FileManifest fileManifest = directive.fileManifest();
    Path generationPath = Path.of(
      fileManifest.getBaseDir() +
      "/" +
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        directive.context().settings().getService().getNamespace()
      )
    );

    /**
     * Smithy ALWAYS writes visited symbols to a file. For wrapped codegen, we do NOT want to write
     * visited symbols to a file. We want to reuse the generated files from localService codegen. It
     * is very, very difficult to change this writing behavior without rewriting Smithy logic in
     * addition to Smithy-Python specific logic. I have tried some workarounds like deleting writers
     * or writing to /dev/null but these were not fruitful. This workaround dumps any visited
     * symbols into a file whose name will never be used and deletes this file as part of its Smithy
     * codegen plugin.
     */
    try {
      LOGGER.info(
        format(
          "Attempting to remove %s.py",
          WrappedCodegenConstants.WRAPPED_CODEGEN_SYMBOLWRITER_DUMP_FILE_FILENAME
        )
      );
      CodegenUtils
        .runCommand(
          format(
            "rm -f %s.py",
            WrappedCodegenConstants.WRAPPED_CODEGEN_SYMBOLWRITER_DUMP_FILE_FILENAME
          ),
          generationPath
        )
        .strip();
    } catch (CodegenException e) {
      // Fail loudly. We do not want to accidentally distribute this file.
      throw new RuntimeException(
        format(
          "Unable to remove %s.py",
          WrappedCodegenConstants.WRAPPED_CODEGEN_SYMBOLWRITER_DUMP_FILE_FILENAME
        ),
        e
      );
    }
  }
}
