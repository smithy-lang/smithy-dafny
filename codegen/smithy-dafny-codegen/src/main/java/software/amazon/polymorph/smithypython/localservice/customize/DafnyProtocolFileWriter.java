// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice.customize;

import java.util.HashSet;
import java.util.Set;
import software.amazon.polymorph.smithypython.common.customize.CustomFileWriter;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.localservice.DafnyLocalServiceCodegenConstants;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/**
 * Writes the dafny_protocol.py file. This file defines the types that are sent to and from the
 * dafnyImplInterface.
 */
public class DafnyProtocolFileWriter implements CustomFileWriter {

  @Override
  public void customizeFileForServiceShape(
    ServiceShape serviceShape,
    GenerationContext codegenContext
  ) {
    String moduleName =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        codegenContext.settings().getService().getNamespace()
      );

    // Collect all `inputShapeIds` to identify all possible types `dafny_operation_input` can take on
    Set<ShapeId> inputShapeIds = new HashSet<>();
    for (ShapeId operationShapeId : serviceShape.getAllOperations()) {
      OperationShape operationShape = codegenContext
        .model()
        .expectShape(operationShapeId, OperationShape.class);
      inputShapeIds.add(operationShape.getInputShape());
    }

    codegenContext
      .writerDelegator()
      .useFileWriter(
        moduleName + "/dafny_protocol.py",
        "",
        writer -> {
          writer.write(
            """
            import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers
            from typing import Union

            class $L:
                operation_name: str

                # dafny_operation_input can take on any one of the types
                # of the input values passed to the Dafny implementation
                dafny_operation_input: Union[
                    ${C|}
                ]

                def __init__(self, operation_name, dafny_operation_input):
                    self.operation_name = operation_name
                    self.dafny_operation_input = dafny_operation_input

            class $L(Wrappers.Result):
                def __init__(self):
                    super().__init__(self)
            """,
            DafnyLocalServiceCodegenConstants.DAFNY_PROTOCOL_REQUEST,
            writer.consumer(w ->
              generateDafnyOperationInputUnionValues(
                inputShapeIds,
                w,
                codegenContext
              )
            ),
            DafnyLocalServiceCodegenConstants.DAFNY_PROTOCOL_RESPONSE
          );
        }
      );
  }

  /**
   * Generates the list of types that compose the Union of types that `dafny_operation_input` can
   * take on.
   *
   * @param inputShapeIds
   * @param writer
   */
  private void generateDafnyOperationInputUnionValues(
    Set<ShapeId> inputShapeIds,
    PythonWriter writer,
    GenerationContext context
  ) {
    // If all operations on the service take no inputs,
    // or if the service has no operations,
    // write `None`
    if (inputShapeIds.isEmpty()) {
      writer.write("None");
    }
    for (ShapeId inputShapeId : inputShapeIds) {
      if (
        context.model().expectShape(inputShapeId).isStructureShape() &&
        context
          .model()
          .expectShape(inputShapeId)
          .asStructureShape()
          .get()
          .hasTrait(PositionalTrait.class)
      ) {} else {
        DafnyNameResolver.importDafnyTypeForShape(
          writer,
          inputShapeId,
          context
        );
        writer.write(
          "$L,",
          DafnyNameResolver.getDafnyTypeForShape(inputShapeId)
        );
      }
    }
  }
}
