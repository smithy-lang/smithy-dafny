// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice.customize;

import software.amazon.polymorph.smithypython.common.customize.CustomFileWriter;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.localservice.DafnyLocalServiceCodegenConstants;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/**
 * Creates a dafnyImplInterface.py file containing a DafnyImplInterface class. This provides a
 * static (here, "unchanging") interface for the Smithy-Python-generated client.py request handler
 * to interact with.
 *
 * <p>(We do this because we cannot extensively customize this part of client.py code generation via
 * the plugin system. Instead, we plug this interface into the part we can customize, and do the
 * rest of the customization in a file we control (this file).)
 */
public class DafnyImplInterfaceFileWriter implements CustomFileWriter {

  @Override
  public void customizeFileForServiceShape(
    ServiceShape serviceShape,
    GenerationContext codegenContext
  ) {
    String moduleName =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        codegenContext.settings().getService().getNamespace()
      );
    String clientName = SmithyNameResolver.clientNameForService(serviceShape);
    String implModulePrelude =
      DafnyNameResolver.getDafnyPythonIndexModuleNameForShape(
        serviceShape,
        codegenContext
      );

    codegenContext
      .writerDelegator()
      .useFileWriter(
        moduleName + "/dafnyImplInterface.py",
        "",
        writer -> {
          writer.write(
            """
            from $L import $L
            from $L import $L

            class DafnyImplInterface:
                $L: $L | None = None

                # operation_map cannot be created at dafnyImplInterface create time,
                # as the map's values reference values inside `self.impl`,
                # and impl is only populated at runtime.
                # Accessing these before impl is populated results in an error.
                # At runtime, the map is populated once and cached.
                operation_map = None

                def handle_request(self, input: DafnyRequest):
                    if self.operation_map is None:
                        self.operation_map = {
                            ${C|}
                        }

                     # This logic is where a typical Smithy client would expect the "server" to be.
                     # This code can be thought of as logic our Dafny "server" uses
                     #   to route incoming client requests to the correct request handler code.
                    if input.dafny_operation_input is None:
                        return self.operation_map[input.operation_name]()
                    else:
                        return self.operation_map[input.operation_name](input.dafny_operation_input)
            """,
            implModulePrelude,
            clientName,
            DafnyLocalServiceCodegenConstants.DAFNY_PROTOCOL_PYTHON_FILENAME,
            DafnyLocalServiceCodegenConstants.DAFNY_PROTOCOL_REQUEST,
            "impl",
            clientName,
            writer.consumer(w ->
              generateImplInterfaceOperationMap(serviceShape, codegenContext, w)
            )
          );
        }
      );
  }

  /**
   * Generates the map from the operation name to the Dafny implementation operation for the
   * provided localService.
   *
   * @param serviceShape
   * @param codegenContext
   * @param writer
   */
  private void generateImplInterfaceOperationMap(
    ServiceShape serviceShape,
    GenerationContext codegenContext,
    PythonWriter writer
  ) {
    for (ShapeId operationShapeId : serviceShape.getOperations()) {
      final OperationShape operationShape = codegenContext
        .model()
        .expectShape(operationShapeId, OperationShape.class);
      writer.write(
        """
        "$L": self.$L.$L,""",
        operationShape.getId().getName(),
        "impl",
        operationShape.getId().getName()
      );
    }
  }
}
