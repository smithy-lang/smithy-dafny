// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.wrappedlocalservice.customize;

import software.amazon.polymorph.smithypython.common.customize.CustomFileWriter;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.common.shapevisitor.ShapeVisitorResolver;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/**
 * Writes the shim.py file. The shim wraps the client.py implementation (which itself wraps the
 * underlying Dafny implementation). Other Dafny-generated Python code may use the shim to interact
 * with this project's Dafny implementation through the Polymorph wrapper.
 */
public class ShimFileWriter implements CustomFileWriter {

  @Override
  public void customizeFileForServiceShape(
    ServiceShape serviceShape,
    GenerationContext codegenContext
  ) {
    String typesModulePrelude =
      DafnyNameResolver.getDafnyPythonTypesModuleNameForShape(
        serviceShape.getId(),
        codegenContext
      );
    String moduleName =
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        codegenContext.settings().getService().getNamespace()
      );
    codegenContext
      .writerDelegator()
      .useFileWriter(
        moduleName + "/shim.py",
        "",
        writer -> {
          writer.addStdlibImport(
            SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
              serviceShape.getId().getNamespace(),
              codegenContext.settings()
            ) +
            ".errors",
            "ServiceError"
          );
          writer.addStdlibImport(
            SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
              serviceShape.getId().getNamespace(),
              codegenContext.settings()
            ) +
            ".errors",
            "CollectionOfErrors"
          );
          writer.addStdlibImport(
            SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
              serviceShape.getId().getNamespace(),
              codegenContext.settings()
            ) +
            ".errors",
            "OpaqueError"
          );

          writer.write(
            """
            import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers
            import $L
            import $L.client as client_impl

            class $L($L.$L):
                def __init__(self, _impl: client_impl) :
                    self._impl = _impl

                ${C|}
            """,
            typesModulePrelude,
            SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
              serviceShape.getId().getNamespace(),
              codegenContext.settings()
            ),
            SmithyNameResolver.shimNameForService(serviceShape),
            typesModulePrelude,
            DafnyNameResolver.getDafnyClientInterfaceTypeForServiceShape(
              serviceShape
            ),
            writer.consumer(w ->
              generateOperationsBlock(codegenContext, serviceShape, w)
            )
          );
        }
      );
  }

  /**
   * Generate shim methods for all operations in the localService. Each method will take in a Dafny
   * type as input and return a Dafny type as output. Internally, each method will convert the Dafny
   * input into native Smithy-modelled input, call the native Smithy client with the native input,
   * receive a native Smithy-modelled output from the client, convert the native output type into
   * its corresponding Dafny type, and return the Dafny type.
   *
   * @param codegenContext
   * @param serviceShape
   * @param writer
   */
  private void generateOperationsBlock(
    GenerationContext codegenContext,
    ServiceShape serviceShape,
    PythonWriter writer
  ) {
    for (ShapeId operationShapeId : serviceShape.getOperations()) {
      OperationShape operationShape = codegenContext
        .model()
        .expectShape(operationShapeId, OperationShape.class);

      // Add imports for operation errors
      for (ShapeId errorShapeId : operationShape.getErrors(serviceShape)) {
        SmithyNameResolver.importSmithyGeneratedTypeForShape(
          writer,
          errorShapeId,
          codegenContext
        );
      }

      ShapeId inputShape = operationShape.getInputShape();
      ShapeId outputShape = operationShape.getOutputShape();

      // Import Dafny types for inputs and outputs (shim function input and output)
      DafnyNameResolver.importDafnyTypeForShape(
        writer,
        inputShape,
        codegenContext
      );
      DafnyNameResolver.importDafnyTypeForShape(
        writer,
        outputShape,
        codegenContext
      );
      // Import Smithy types for inputs and outputs (Smithy client call input and output)
      SmithyNameResolver.importSmithyGeneratedTypeForShape(
        writer,
        inputShape,
        codegenContext
      );
      SmithyNameResolver.importSmithyGeneratedTypeForShape(
        writer,
        outputShape,
        codegenContext
      );

      writer.addStdlibImport("typing", "Any");

      // Write the Shim operation block.
      // This takes in a Dafny input and returns a Dafny output.
      // This operation will:
      //  1) Convert the Dafny input to a Smithy-modelled input,
      //  2) Call the Smithy-generated client with the transformed input, and
      //  3) Convert the Smithy output to the Dafny type.
      writer.openBlock(
        "def $L(self, $L):",
        "",
        operationShape.getId().getName(),
        // Do not generate an `input` parameter if the operation does not take in an input
        SmithyNameResolver.isUnitShape(inputShape) ? "" : "input",
        () -> {
          Shape targetShapeInput = codegenContext
            .model()
            .expectShape(operationShape.getInputShape());
          // Generate code that converts the input from the Dafny type to the corresponding Smithy
          // type.
          // `input` will hold a string that converts the Dafny `input` to the Smithy-modelled
          // output.
          String input = targetShapeInput.accept(
            ShapeVisitorResolver.getToNativeShapeVisitorForShape(
              targetShapeInput,
              codegenContext,
              "input",
              writer
            )
          );

          Shape targetShape = codegenContext
            .model()
            .expectShape(operationShape.getOutputShape());
          // Generate code that converts the output from Smithy type to the corresponding Dafny
          // type.
          // This has a side effect of possibly writing transformation code at the writer's
          // current position.
          String output = targetShape.accept(
            ShapeVisitorResolver.getToDafnyShapeVisitorForShape(
              targetShape,
              codegenContext,
              "smithy_client_response",
              writer
            )
          );

          // Generate code that:
          // 1) "unwraps" the request (converts from the Dafny type to the Smithy type),
          // 2) calls Smithy client,
          // 3) wraps Smithy failures as Dafny failures
          writer.write(
            """
            try:
                smithy_client_request: $L.$L = $L
                smithy_client_response = self._impl.$L(smithy_client_request)
                return Wrappers.Result_Success($L)
            except Exception as e:
                return Wrappers.Result_Failure(_smithy_error_to_dafny_error(e))
            """,
            SmithyNameResolver.getSmithyGeneratedModelLocationForShape(
              inputShape,
              codegenContext
            ),
            inputShape.getName(),
            input,
            codegenContext.symbolProvider().toSymbol(operationShape).getName(),
            SmithyNameResolver.isUnitShape(outputShape) ? "None" : output
          );

          writer.addStdlibImport(
            SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
              serviceShape.getId().getNamespace(),
              codegenContext.settings()
            ) +
            ".errors",
            "_smithy_error_to_dafny_error"
          );
        }
      );
    }
  }
}
