// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.wrappedlocalservice.customize;

import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

import software.amazon.polymorph.smithypython.awssdk.nameresolver.AwsSdkNameResolver;
import software.amazon.polymorph.smithypython.common.customize.CustomFileWriter;
import software.amazon.polymorph.smithypython.common.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.Utils;
import software.amazon.polymorph.smithypython.common.shapevisitor.ShapeVisitorResolver;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.traits.ErrorTrait;
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
      ServiceShape serviceShape, GenerationContext codegenContext) {
    String typesModulePrelude =
        DafnyNameResolver.getDafnyPythonTypesModuleNameForShape(serviceShape.getId());
    String moduleName =
        SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
            codegenContext.settings().getService().getNamespace());
    codegenContext
        .writerDelegator()
        .useFileWriter(
            moduleName + "/shim.py",
            "",
            writer -> {
              writer.addImport(".errors", "ServiceError");
              writer.addImport(".errors", "CollectionOfErrors");
              writer.addImport(".errors", "OpaqueError");

              writer.write(
                  """
          import Wrappers
          import $L
          import $L.client as client_impl
          
          def _smithy_error_to_dafny_error(e: ServiceError):
                 '''
                 Converts the provided native Smithy-modelled error
                 into the corresponding Dafny error.
                 '''
                 ${C|}

          class $L($L.$L):
              def __init__(self, _impl: client_impl) :
                  self._impl = _impl

              ${C|}
              """,
                  typesModulePrelude,
                  SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
                      serviceShape.getId().getNamespace(), codegenContext.settings()),
                  writer.consumer(
                      w -> generateSmithyErrorToDafnyErrorBlock(codegenContext, serviceShape, w)),
                  SmithyNameResolver.shimNameForService(serviceShape),
                  typesModulePrelude,
                  DafnyNameResolver.getDafnyClientInterfaceTypeForServiceShape(serviceShape),
                  writer.consumer(w -> generateOperationsBlock(codegenContext, serviceShape, w))
              );
        });
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
      GenerationContext codegenContext, ServiceShape serviceShape, PythonWriter writer) {

    for (ShapeId operationShapeId : serviceShape.getOperations()) {
      OperationShape operationShape =
          codegenContext.model().expectShape(operationShapeId, OperationShape.class);

      // Add imports for operation errors
      for (ShapeId errorShapeId : operationShape.getErrors(serviceShape)) {
        SmithyNameResolver.importSmithyGeneratedTypeForShape(writer, errorShapeId, codegenContext);
      }

      ShapeId inputShape = operationShape.getInputShape();
      ShapeId outputShape = operationShape.getOutputShape();

      // Import Dafny types for inputs and outputs (shim function input and output)
      DafnyNameResolver.importDafnyTypeForShape(writer, inputShape, codegenContext);
      DafnyNameResolver.importDafnyTypeForShape(writer, outputShape, codegenContext);
      // Import Smithy types for inputs and outputs (Smithy client call input and output)
      SmithyNameResolver.importSmithyGeneratedTypeForShape(writer, inputShape, codegenContext);
      SmithyNameResolver.importSmithyGeneratedTypeForShape(writer, outputShape, codegenContext);

      boolean isInputPositional =
          codegenContext
              .model()
              .expectShape(inputShape)
              .asStructureShape()
              .get()
              .hasTrait(PositionalTrait.class);
      boolean isOutputPoitional =
          codegenContext
              .model()
              .expectShape(inputShape)
              .asStructureShape()
              .get()
              .hasTrait(PositionalTrait.class);

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
          Utils.isUnitShape(inputShape) ? "" : "input",
          () -> {
            Shape targetShapeInput =
                codegenContext.model().expectShape(operationShape.getInputShape());
            // Generate code that converts the input from the Dafny type to the corresponding Smithy
            // type.
            // `input` will hold a string that converts the Dafny `input` to the Smithy-modelled
            // output.
            String input =
                targetShapeInput.accept(
                    ShapeVisitorResolver.getToNativeShapeVisitorForShape(
                        targetShapeInput, codegenContext, "input", writer));

            // Generate code that:
            // 1) "unwraps" the request (converts from the Dafny type to the Smithy type),
            // 2) calls Smithy client,
            // 3) wraps Smithy failures as Dafny failures
            writer.write(
                """
              smithy_client_request: $L.$L = $L
              try:
                  smithy_client_response = self._impl.$L(smithy_client_request)
              except ServiceError as e:
                  return Wrappers.Result_Failure(_smithy_error_to_dafny_error(e))

              """,
                SmithyNameResolver.getSmithyGeneratedModelLocationForShape(inputShape, codegenContext),
                inputShape.getName(),
                input,
                codegenContext.symbolProvider().toSymbol(operationShape).getName());

            Shape targetShape = codegenContext.model().expectShape(operationShape.getOutputShape());
            // Generate code that converts the output from Smithy type to the corresponding Dafny
            // type.
            // This has a side effect of possibly writing transformation code at the writer's
            // current position.
            String output =
                targetShape.accept(
                    ShapeVisitorResolver.getToDafnyShapeVisitorForShape(
                        targetShape, codegenContext, "smithy_client_response", writer));

            // Generate code that wraps Smithy success shapes as Dafny success shapes
            writer.write(
                """
                return Wrappers.Result_Success($L)
                """,
                Utils.isUnitShape(outputShape) ? "None" : output);
          });
    }
  }

    /**
     * Generate the method body for the `_smithy_error_to_dafny_error` method.
     *
     * @param codegenContext
     * @param serviceShape
     * @param writer
     */
    private void generateSmithyErrorToDafnyErrorBlock(
            GenerationContext codegenContext, ServiceShape serviceShape, PythonWriter writer) {

        // Write modelled error converters for this service
        TreeSet<ShapeId> errorShapeSet =
                new TreeSet<ShapeId>(
                        codegenContext.model().getStructureShapesWithTrait(ErrorTrait.class).stream()
                                .filter(
                                        structureShape ->
                                                structureShape
                                                        .getId()
                                                        .getNamespace()
                                                        .equals(codegenContext.settings().getService().getNamespace()))
                                .map(Shape::getId)
                                .collect(Collectors.toSet()));
        for (ShapeId errorShapeId : errorShapeSet) {
            SmithyNameResolver.importSmithyGeneratedTypeForShape(writer, errorShapeId, codegenContext);
            writer.addStdlibImport(DafnyNameResolver.getDafnyPythonTypesModuleNameForShape(errorShapeId));
            writer.write(
                    """
                        if isinstance(e, $L.$L):
                            return $L.$L(message=e.message)
                        """,
                    SmithyNameResolver.getSmithyGeneratedModelLocationForShape(errorShapeId, codegenContext),
                    errorShapeId.getName(),
                    DafnyNameResolver.getDafnyPythonTypesModuleNameForShape(errorShapeId),
                    DafnyNameResolver.getDafnyTypeForError(errorShapeId));
        }

        // Write out wrapping errors for dependencies.
        // This service will generate a dependency-specific error for each dependency.
        // This dependency-specific error generated for only this service, and not for the dependency
        // service;
        //   this error type will wrap any dependency service's error for processing by this service.
        // The Dafny type for this error contains one member: the dependency's name.
        // ex. Dafny type for MyDependency: `Error_MyDependency(Error...) = { MyDependency: ... }`
        // This member's value can take on any of the error types modelled in the dependency.
        // Polymorph will generate a similar error structure in the primary service's errors.py file.
        // ex. Smithy type for MyDependency: `MyDependency(ApiError...) = { MyDependency: ... }`
        Optional<LocalServiceTrait> maybeLocalServiceTrait =
                serviceShape.getTrait(LocalServiceTrait.class);
        if (maybeLocalServiceTrait.isPresent()) {
            LocalServiceTrait localServiceTrait = maybeLocalServiceTrait.get();
            Set<ShapeId> serviceDependencyShapeIds = localServiceTrait.getDependencies();

            if (serviceDependencyShapeIds != null) {
                for (ShapeId serviceDependencyShapeId : serviceDependencyShapeIds) {

                    ServiceShape dependencyServiceShape = codegenContext
                            .model()
                            .expectShape(serviceDependencyShapeId)
                            .asServiceShape()
                            .get();

                    String nativeToDafnyErrorName;
                    String conversionFilename;
                    if (dependencyServiceShape.hasTrait(LocalServiceTrait.class)) {
                        nativeToDafnyErrorName = "_smithy_error_to_dafny_error";
                    } else if (AwsSdkNameResolver.isAwsSdkShape(dependencyServiceShape)) {
                        nativeToDafnyErrorName = "_sdk_error_to_dafny_error";
                    } else {
                        throw new IllegalArgumentException("Provided serviceShape is neither localService nor AWS SDK shape: " + dependencyServiceShape);
                    }

                    // Import the dependency service's `_smithy_error_to_dafny_error` so this service
                    //   can defer error conversion to the dependency
                    writer.addStdlibImport(
                            SmithyNameResolver.getPythonModuleSmithygeneratedPathForSmithyNamespace(
                                    serviceDependencyShapeId.getNamespace(), codegenContext.settings())
                                    + ".shim",
                            nativeToDafnyErrorName,
                            SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
                                    serviceDependencyShapeId.getNamespace())
                                    + nativeToDafnyErrorName);

                    // Import this service's error that wraps the dependency service's errors
                    ServiceShape serviceDependencyShape = codegenContext.model().expectShape(serviceDependencyShapeId).asServiceShape().get();
                    String dependencyErrorName = SmithyNameResolver.getSmithyGeneratedTypeForServiceError(serviceDependencyShape);
                    System.out.println("importing " + dependencyErrorName);
                    writer.addImport(".errors", dependencyErrorName);
                    // Generate conversion method that says:
                    // "If this is a dependency-specific error, defer to the dependency's
                    // `_smithy_error_to_dafny_error`"
                    // if isinstance(e, MyDependency):
                    //   return
                    // MyService.Error_MyDependency(MyDependency_smithy_error_to_dafny_error(e.message))
                    writer.write(
                            """
                                if isinstance(e, $L):
                                    return $L.Error_$L($L(e.message))
                                """,
                            dependencyErrorName,
                            DafnyNameResolver.getDafnyPythonTypesModuleNameForShape(serviceShape),
                            dependencyErrorName,
                            SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
                                    serviceDependencyShapeId.getNamespace())
                                    + nativeToDafnyErrorName);
                }
            }
        }

        // Add service-specific CollectionOfErrors
        writer.write(
                """
                    if isinstance(e, CollectionOfErrors):
                        return $L.Error_CollectionOfErrors(message=e.message, list=e.list)
                    """,
                DafnyNameResolver.getDafnyPythonTypesModuleNameForShape(serviceShape.getId()));
        // Add service-specific OpaqueError
        writer.write(
                """
                    if isinstance(e, OpaqueError):
                        return $L.Error_Opaque(obj=e.obj)
                    """,
                DafnyNameResolver.getDafnyPythonTypesModuleNameForShape(serviceShape.getId()));
    }
}
