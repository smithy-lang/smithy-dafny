package software.amazon.polymorph.smithypython.customize;

import java.util.HashSet;
import java.util.Set;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;


/**
 * Extends the Smithy-Python-generated models.py file
 * by adding Dafny plugin models.
 */
public class ModelsFileWriter implements CustomFileWriter {
  @Override
  public void generateFileForServiceShape(
      ServiceShape serviceShape, GenerationContext codegenContext) {
    String moduleName = codegenContext.settings().getModuleName();

    final LocalServiceTrait localServiceTrait = serviceShape.expectTrait(LocalServiceTrait.class);
    final StructureShape configShape = codegenContext.model().expectShape(localServiceTrait.getConfigId(), StructureShape.class);
    System.out.println(configShape.getAllMembers());


    /*
        blob_value: Any
        boolean_value: Any
        string_value: Any
        integer_value: Any
        long_value: Any

        def __init__(self, blob_value, boolean_value, string_value, integer_value, long_value):
            self.long_value = long_value
            self.blob_value = blob_value
            self.boolean_value = boolean_value
            self.string_value = string_value
            self.integer_value = integer_value
     */

    // TODO: Ideally I don't need to do this, but this almost seems necessary
    // to avoid having to fork Smithy-Python...
    codegenContext.writerDelegator().useFileWriter(moduleName + "/models.py", "", writer -> {
      writer.write(
          """
             ${C|}
             
             class Unit:
                 pass
              """,
          writer.consumer(w -> generateServiceOperationModelShapes(codegenContext, serviceShape, w))
      );
    });
  }

  private void generateServiceOperationModelShapes(
      GenerationContext codegenContext, ServiceShape serviceShape, PythonWriter writer) {

    Set<ShapeId> inputShapeIds = new HashSet<>();
    Set<ShapeId> outputShapeIds = new HashSet<>();
    for (ShapeId operationShapeId : serviceShape.getOperations()) {
      OperationShape operationShape = codegenContext.model()
          .expectShape(operationShapeId, OperationShape.class);
      inputShapeIds.add(operationShape.getInputShape());
      outputShapeIds.add(operationShape.getOutputShape());
    }

    Set<MemberShape> referenceMemberShapes = new HashSet<>();
    referenceMemberShapes.addAll(
        ModelUtils.findAllDependentMemberReferenceShapes(inputShapeIds, codegenContext.model()));
    referenceMemberShapes.addAll(
        ModelUtils.findAllDependentMemberReferenceShapes(outputShapeIds, codegenContext.model()));

    // TODO: Separate service vs resource shapes
    Set<Shape> referenceChildShape = new HashSet<>();
    for (MemberShape referenceMemberShape : referenceMemberShapes) {
      Shape referenceShape = codegenContext.model().expectShape(referenceMemberShape.getTarget());
      ReferenceTrait referenceTrait = referenceShape.expectTrait(ReferenceTrait.class);
      System.out.println(referenceTrait.getReferentId());
      Shape resourceOrService = codegenContext.model().expectShape(referenceTrait.getReferentId());
      referenceChildShape.add(resourceOrService);
    }

    for(Shape resourceOrService : referenceChildShape) {
      writer.write("""
        class $L:
            _impl: Any
            
            def __init__(self, _impl):
                self._impl = _impl
                
            ${C|}
        """,
          resourceOrService.getId().getName(),
          writer.consumer(w -> generateSmithyOperationFunctionDefinitionForResource(
              codegenContext, resourceOrService, w)
          )
      );
    }
  }

  private void generateSmithyOperationFunctionDefinitionForResource(
      GenerationContext codegenContext, Shape resourceOrService, PythonWriter writer) {
    for (ShapeId operationShapeId : resourceOrService.asResourceShape().get().getOperations()) {
      writer.write("""
          def $L(self, dafny_input):
              return self._impl.$L(dafny_input)
          """, operationShapeId.getName(), operationShapeId.getName());
    }
  }


}
