// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.wrappedlocalservice.extensions;

import static java.lang.String.format;

import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.localservice.extensions.DafnyPythonLocalServiceSymbolVisitor;
import software.amazon.polymorph.smithypython.wrappedlocalservice.WrappedCodegenConstants;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.python.codegen.PythonSettings;

/**
 * SymbolVisitor for wrapped localService codegen.
 *
 * Overrides the generated file for codegen to something that is immediately deleted.
 * Smithy ALWAYS writes visited symbols to a file. For wrapped codegen,
 * we do NOT want to write visited symbols to a file. We want to reuse the
 * generated files from localService codegen.
 *
 * It is very, very difficult to change this writing
 * behavior without rewriting Smithy logic, in addition to Smithy-Python specific logic. I have tried
 * some workarounds like deleting writers or writing to /dev/null but these were not fruitful. This
 * workaround dumps any visited symbols into a file whose name will never be used and deletes this
 * file as part of its Smithy codegen plugin.
 */
public class DafnyPythonWrappedLocalServiceSymbolVisitor
  extends DafnyPythonLocalServiceSymbolVisitor {

  public DafnyPythonWrappedLocalServiceSymbolVisitor(
    Model model,
    PythonSettings settings
  ) {
    super(model, settings);
  }

  /**
   * Path to the overridden file that is deleted for wrapped services.
   *
   * @param namespace
   * @return
   */
  @Override
  protected String getSymbolDefinitionFilePathForNamespaceAndFilename(
    String namespace,
    String filename
  ) {
    String directoryFilePath;
    if ("smithy.api".equals(namespace)) {
      directoryFilePath =
        SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
          settings.getService().getNamespace()
        );
    } else {
      directoryFilePath =
        SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
          namespace
        );
    }

    // Wrapped codegen deletes this file.
    return format(
      "%s/%s.py",
      directoryFilePath,
      WrappedCodegenConstants.WRAPPED_CODEGEN_SYMBOLWRITER_DUMP_FILE_FILENAME
    );
  }
}
