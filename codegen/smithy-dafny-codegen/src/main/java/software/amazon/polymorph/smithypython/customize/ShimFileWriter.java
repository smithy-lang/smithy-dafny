package software.amazon.polymorph.smithypython.customize;

import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.smithypython.shapevisitor.DafnyToSmithyShapeVisitor;
import software.amazon.polymorph.smithypython.shapevisitor.SmithyToDafnyShapeVisitor;
import software.amazon.polymorph.smithypython.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.nameresolver.Utils;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/**
 * Writes the shim.py file.
 * The shim wraps the client.py implementation (which itself wraps the underlying Dafny implementation).
 * Other Dafny-generated Python code will use the Shim class to interact with this project's Dafny implementation.
 */
public class ShimFileWriter implements CustomFileWriter {

  @Override
  public void customizeFileForServiceShape(
      ServiceShape serviceShape, GenerationContext codegenContext) {
    String typesModulePrelude = DafnyNameResolver.getDafnyTypesModuleNamespaceForShape(serviceShape.getId());
    String moduleName = codegenContext.settings().getModuleName();
    codegenContext.writerDelegator().useFileWriter(moduleName + "/shim.py", "", writer -> {
      writer.addImport(".errors", "ServiceError");
      writer.addImport(".errors", "CollectionOfErrors");
      writer.addImport(".errors", "OpaqueError");

      writer.write(
          """
          import Wrappers
          import asyncio
          import $L
          import $L.smithygenerated.client as client_impl
                          
          def smithy_error_to_dafny_error(e: ServiceError):
              ${C|}
                          
          class $L($L.$L):
              def __init__(self, _impl: client_impl) :
                  self._impl = _impl
                          
              ${C|}
              
              """, typesModulePrelude, moduleName,
          writer.consumer(w -> generateErrorsBlock(codegenContext, serviceShape, w)),
          SmithyNameResolver.shimForService(serviceShape),
          typesModulePrelude, DafnyNameResolver.getDafnyClientInterfaceTypeForServiceShape(serviceShape),
          writer.consumer(w -> generateOperationsBlock(codegenContext, serviceShape, w))
      );
    });
  }

  private void generateErrorsBlock(
      GenerationContext codegenContext, ServiceShape serviceShape, PythonWriter writer) {

    // Write modelled error converters

    var errorShapeSet = new TreeSet<ShapeId>(
        codegenContext.model().getStructureShapesWithTrait(ErrorTrait.class)
            .stream()
            .filter(structureShape -> structureShape.getId().getNamespace()
                .equals(codegenContext.settings().getService().getNamespace()))
            .map(Shape::getId)
            .collect(Collectors.toSet()));

    System.out.println(errorShapeSet);

    for (ShapeId errorShapeId : errorShapeSet) {
      writer.addImport(SmithyNameResolver.getSmithyGeneratedModuleNamespaceForSmithyNamespace(
          errorShapeId.getNamespace(),
          codegenContext
      ) + ".errors", errorShapeId.getName());
      writer.write("""
              if isinstance(e, $L):
                  return $L.$L(message=e.message)
              """,
          errorShapeId.getName(),
          DafnyNameResolver.getDafnyTypesModuleNamespaceForShape(errorShapeId),
          DafnyNameResolver.getDafnyTypeForError(errorShapeId)
      );
    }

    // Dependency errors
    LocalServiceTrait localServiceTrait = serviceShape.getTrait(LocalServiceTrait.class).get();
    Set<ShapeId> serviceDependencyShapeIds = localServiceTrait.getDependencies();
    for (ShapeId serviceDependencyShapeId : serviceDependencyShapeIds) {
      writer.addImport(
          SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(serviceDependencyShapeId.getNamespace())
              + ".smithygenerated.shim",
          "smithy_error_to_dafny_error",
          SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(serviceDependencyShapeId.getNamespace())
              + "_smithy_error_to_dafny_error"
      );
      writer.write("""
              if isinstance(e, $L):
                  return $L.Error_$L($L(e.message))
              """,
          serviceDependencyShapeId.getName(),
          DafnyNameResolver.getDafnyTypesModuleNamespaceForShape(serviceShape),
          serviceDependencyShapeId.getName(),
          SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(serviceDependencyShapeId.getNamespace())
              + "_smithy_error_to_dafny_error"
      );
      writer.addImport(".errors", serviceDependencyShapeId.getName());
    }

    // Add service-specific CollectionOfErrors
    writer.write("""
            if isinstance(e, CollectionOfErrors):
                return $L.Error_CollectionOfErrors(message=e.message, list=e.list)
            """,
        DafnyNameResolver.getDafnyTypesModuleNamespaceForShape(serviceShape.getId())
    );
    // Add service-specific OpaqueError
    writer.write("""
            if isinstance(e, OpaqueError):
                return $L.Error_Opaque(obj=e.obj)
            """,
        DafnyNameResolver.getDafnyTypesModuleNamespaceForShape(serviceShape.getId())
    );
  }

  private void generateOperationsBlock(
      GenerationContext codegenContext, ServiceShape serviceShape, PythonWriter writer) {

    for (ShapeId operationShapeId : serviceShape.getOperations()) {
      OperationShape operationShape = codegenContext.model().expectShape(operationShapeId, OperationShape.class);

      // Add imports for operation errors
      for (ShapeId errorShapeId : operationShape.getErrors(serviceShape)) {
        writer.addImport(SmithyNameResolver.getSmithyGeneratedModuleNamespaceForSmithyNamespace(
            errorShapeId.getNamespace(),
            codegenContext
        ) + ".errors", errorShapeId.getName());
      }

      ShapeId inputShape = operationShape.getInputShape();
      ShapeId outputShape = operationShape.getOutputShape();

      String dafnyInputType = DafnyNameResolver.getDafnyTypeForShape(inputShape);
      String dafnyOutputType = DafnyNameResolver.getDafnyTypeForShape(outputShape);
      String operationSymbol = codegenContext.symbolProvider().toSymbol(operationShape).getName();

      System.out.println("inputShape: " + inputShape);
      System.out.println(SmithyNameResolver.getSmithyGeneratedModuleNamespaceForSmithyNamespace(
              inputShape.getNamespace(), codegenContext));
      System.out.println("outputShape: " + outputShape);
      System.out.println(SmithyNameResolver.getSmithyGeneratedModuleNamespaceForSmithyNamespace(
          outputShape.getNamespace(),codegenContext ));


      DafnyNameResolver.importDafnyTypeForShape(writer, inputShape);
      DafnyNameResolver.importDafnyTypeForShape(writer, outputShape);
      writer.addImport(
          SmithyNameResolver.getSmithyGeneratedModuleNamespaceForSmithyNamespace(
            inputShape.getNamespace(), codegenContext
          ) + ".models", inputShape.getName()
      );
      writer.addImport(
          SmithyNameResolver.getSmithyGeneratedModuleNamespaceForSmithyNamespace(
            outputShape.getNamespace(), codegenContext
          ) + ".models", outputShape.getName()
      );

      writer.openBlock("def $L(self, $L) -> $L:", "",
          operationShape.getId().getName(),
          Utils.isUnitShape(inputShape) ? "" : "input: " + dafnyInputType,
          Utils.isUnitShape(outputShape) ? "None" : dafnyOutputType,
          () -> {

            Shape targetShapeInput = codegenContext.model().expectShape(operationShape.getInputShape());
            // Generate code that converts the input from the Dafny type to the corresponding Smithy type
            // This has a side effect of writing any transformation code
            var input = targetShapeInput.accept(new DafnyToSmithyShapeVisitor(
                codegenContext,
                "input",
                writer,
                false
            ));

            writer.write("""
          unwrapped_request: $L = $L
          try:
              wrapped_response = asyncio.run(self._impl.$L(unwrapped_request))
          except ServiceError as e:
              return Wrappers.Result_Failure(smithy_error_to_dafny_error(e))
                  
          """,
                inputShape.getName(),
                input,
                operationSymbol);

            Shape targetShape = codegenContext.model().expectShape(operationShape.getOutputShape());
            // Generate code that converts the output from Smithy type to the corresponding Dafny type
            // This has a side effect of writing any transformation code
            String output = targetShape.accept(new SmithyToDafnyShapeVisitor(
                codegenContext,
                "wrapped_response",
                writer,
                false
            ));

            writer.write("""
          return Wrappers.Result_Success($L)
          """,
                Utils.isUnitShape(outputShape) ? "None" : output);
          }

      );
    }
  }
}
