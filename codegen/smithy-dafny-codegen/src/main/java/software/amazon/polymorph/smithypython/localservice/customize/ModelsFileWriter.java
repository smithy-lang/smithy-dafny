// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice.customize;

import software.amazon.polymorph.smithypython.common.customize.CustomFileWriter;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.python.codegen.GenerationContext;

/** Extends the Smithy-Python-generated models.py file by adding Dafny plugin models. */
public class ModelsFileWriter implements CustomFileWriter {

  @Override
  public void customizeFileForServiceShape(
    ServiceShape serviceShape,
    GenerationContext codegenContext
  ) {
    String moduleName =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        codegenContext.settings().getService().getNamespace()
      );
    codegenContext
      .writerDelegator()
      .useFileWriter(
        moduleName + "/models.py",
        "",
        writer -> {
          // This block defines an empty `Unit` class used by Smithy-Python generated code
          // Defining this seems necessary to avoid forking Smithy-Python
          // TODO-Python: Find some way to not need this, or decide this is OK. Low priority
          writer.write(
            """
            class Unit:
                pass
             """
          );
        }
      );
  }
}
