package software.amazon.polymorph.smithypython.customize;

import static software.amazon.polymorph.smithypython.nameresolver.PythonNameResolver.shimForService;

import java.util.HashSet;
import java.util.Set;
import java.util.TreeSet;
import software.amazon.polymorph.smithypython.DafnyProtocolGenerator.DafnyMemberDeserVisitor;
import software.amazon.polymorph.smithypython.DafnyProtocolGenerator.DafnyMemberSerVisitor;
import software.amazon.polymorph.smithypython.nameresolver.DafnyNameResolver;
import software.amazon.polymorph.smithypython.nameresolver.Utils;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.python.codegen.GenerationContext;

public class ShimFileWriter implements CustomFileWriter {

  @Override
  public void generateFileForServiceShape(
      ServiceShape serviceShape, GenerationContext codegenContext) {
    // TODO: refactor to DafnyProtocolFileWriter
    // TODO: Naming of this file?

    // TODO: StringBuilder
        /*
        TODO: This is what this SHOULD look like after getting some sort of TypeConversion in
                        unwrapped_request = TypeConversion.ToNative(input)
                        try:
                            wrapped_response = self._impl.get_integer(unwrapped_request)
                            return Wrappers_Compile.Result_Success(wrapped_response)
                        catch ex:
                            return Wrappers_Compile.Result_Failure(ex)
         */
    String operationsShim = "";
    String errorsString = "";
    Set<ShapeId> allInputShapesSet = new HashSet<>();
    Set<ShapeId> allOutputShapesSet = new HashSet<>();
    var deserializingErrorShapes = new TreeSet<ShapeId>();
    var service = codegenContext.settings().getService(codegenContext.model());
    String typesModulePrelude = DafnyNameResolver.getDafnyTypesModuleNamespaceForShape(serviceShape.getId());

    // TODO: .getAllOperations? Maybe .getOperations? or .getIntroducedOperations?
    // Might learn which one when working on Resources
    for (ShapeId operationShapeId : service.getAllOperations()) {
      OperationShape operationShape = codegenContext.model().expectShape(operationShapeId, OperationShape.class);
      deserializingErrorShapes.addAll(operationShape.getErrors(service));
      allInputShapesSet.add(operationShape.getInputShape());
      allOutputShapesSet.add(operationShape.getOutputShape());

      ShapeId inputShape = operationShape.getInputShape();
      ShapeId outputShape = operationShape.getOutputShape();

      String dafnyInputType = DafnyNameResolver.getDafnyTypeForShape(inputShape);
      String dafnyOutputType = DafnyNameResolver.getDafnyTypeForShape(outputShape);
      String operationSymbol = codegenContext.symbolProvider().toSymbol(operationShape).getName();

      Shape targetShape = codegenContext.model().expectShape(operationShape.getOutputShape());
      var output = targetShape.accept(new DafnyMemberDeserVisitor(
          codegenContext,
          "wrapped_response",
          true
      ));

      Shape targetShapeInput = codegenContext.model().expectShape(operationShape.getInputShape());
      var input = targetShapeInput.accept(new DafnyMemberSerVisitor(
          codegenContext,
          "input",
          false
      ));

      operationsShim += """
                    def %1$s(self, %2$s) -> %3$s:
                            unwrapped_request: %4$s = %4$s(%6$s)
                            try:
                                wrapped_response = asyncio.run(self._impl.%5$s(unwrapped_request))
                            except ServiceError as e:
                                return Wrappers_Compile.Result_Failure(smithy_error_to_dafny_error(e))
                            return Wrappers_Compile.Result_Success(%3$s%7$s)
                """.formatted(
          operationShape.getId().getName(),
          Utils.isUnitShape(inputShape) ? "" : "input: " + dafnyInputType,
          Utils.isUnitShape(outputShape) ? "None" : dafnyOutputType,
          inputShape.getName(),
          operationSymbol,
          input,
          Utils.isUnitShape(outputShape) ? "" : "(" + output + ")"
      );
    }
    String allOperationsShim = operationsShim;

    // TODO: StringBuilder? Writer?
    for (ShapeId errorShape : deserializingErrorShapes) {
      errorsString += """
                    if isinstance(e, %1$s):
                        return %2$s%3$s(message=e.message)
                """.formatted(
          errorShape.getName(),
          errorShape.getNamespace() + ".internaldafny.types.",
          "Error_" + errorShape.getName()
      );
    }

    errorsString += """
                    if isinstance(e, CollectionOfErrors):
                        return %1$sError_CollectionOfErrors(message=e.message, list=e.list)
                """.formatted(
        service.getId().getNamespace() + ".internaldafny.types."
    );

    errorsString += """
                    if isinstance(e, OpaqueError):
                        return %1$sError_Opaque(obj=e.obj)
                """.formatted(
        service.getId().getNamespace() + ".internaldafny.types."
    );

    final String finalErrorsString = errorsString;

    String moduleName =  codegenContext.settings().getModuleName();
    codegenContext.writerDelegator().useFileWriter(moduleName + "/shim.py", "", writer -> {
      for (ShapeId inputShapeId : allInputShapesSet) {
        writer.addImport(".models", inputShapeId.getName());
        DafnyNameResolver.importDafnyTypeForShape(writer, inputShapeId);
      }

      for (ShapeId outputShapeId : allOutputShapesSet) {
        DafnyNameResolver.importDafnyTypeForShape(writer, outputShapeId);
      }

      writer.addImport(".errors", "ServiceError");
      writer.addImport(".errors", "CollectionOfErrors");
      writer.addImport(".errors", "OpaqueError");

      for (ShapeId errorShapeId : deserializingErrorShapes) {
        writer.addImport(".errors", errorShapeId.getName());
      }

      writer.write(
          """
          import Wrappers_Compile
          import asyncio
          import $L
          import $L.smithy_generated.$L.client as client_impl
         
                          
          def smithy_error_to_dafny_error(e: ServiceError):
          $L
                          
          class $L($L.$L):
              def __init__(self, _impl: client_impl) :
                  self._impl = _impl
                          
          $L
              
              """, typesModulePrelude, moduleName, moduleName, finalErrorsString, shimForService(serviceShape),
          typesModulePrelude, "I" + serviceShape.getId().getName() + "Client", allOperationsShim
      );
    });
  }
}
