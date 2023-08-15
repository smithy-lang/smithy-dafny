package software.amazon.polymorph.smithypython.customize;

import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
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
    codegenContext.writerDelegator().useFileWriter(moduleName + "/models.py", "", writer -> {

      // This block defines an empty `Unit` class used by Smithy-Python generated code
      // Defining this seems necessary to avoid forking Smithy-Python
      // TODO: Find some way to not need this, or decide this is OK
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

    // Parse operation input and output shapes to retrieve any reference shapes
    Set<ShapeId> inputAndOutputShapeIds = new HashSet<>();
    for (ShapeId operationShapeId : serviceShape.getOperations()) {
      OperationShape operationShape = codegenContext.model()
          .expectShape(operationShapeId, OperationShape.class);
      inputAndOutputShapeIds.add(operationShape.getInputShape());
      inputAndOutputShapeIds.add(operationShape.getOutputShape());
    }
    Set<MemberShape> referenceMemberShapes = new HashSet<>();
    referenceMemberShapes.addAll(
        ModelUtils.findAllDependentMemberReferenceShapes(inputAndOutputShapeIds, codegenContext.model()));

    // Parse reference shapes to retrieve the underlying Resource or Service shape
    // TODO: Separate service vs resource shapes
    Set<Shape> referenceChildShape = new HashSet<>();
    for (MemberShape referenceMemberShape : referenceMemberShapes) {
      Shape referenceShape = codegenContext.model().expectShape(referenceMemberShape.getTarget());
      ReferenceTrait referenceTrait = referenceShape.expectTrait(ReferenceTrait.class);
      Shape resourceOrService = codegenContext.model().expectShape(referenceTrait.getReferentId());
      referenceChildShape.add(resourceOrService);
    }

    // For each reference shape, generate an interface and an implementation shape
    for(Shape resourceOrServiceShape : referenceChildShape) {
      // TODO: Services
      // Write reference interface.
      // We use the `abc` (Abstract Base Class) library to define a stricter interface contract
      //   for references in Python than a standard Python subclass contract.
      // The generated code will use the ABC library to enforce constraints at object-create time.
      // In particular, when the object is constructed, the constructor will validate that the
      //   object's class implements all callable operations defined in the reference's Smithy model.
      // This differs from standard Python duck-typing, where classes implementing an "interface" are
      //   only checked that an "interface" operation is implemented at operation call-time.
      // We do this for a number of reasons:
      //   1) This is a Smithy-Dafny code generator, and Dafny has this stricter interface
      //      contract. We decide to generate code that biases toward the Dafny behavior;
      //   2) A strict interface contract will detect issues implementing an interface sooner.
      // This is opinionated and may change.
      writer.addStdlibImport("abc");
      writer.write("""
        
        class I$L(metaclass=abc.ABCMeta):
            @classmethod
            def __subclasshook__(cls, subclass):
                return (
                    ${C|}
                )
                
            # TODO: Add impl with typehint to ABC
                
            ${C|}
        """,
          resourceOrServiceShape.getId().getName(),
          writer.consumer(w -> generateInterfaceSubclasshookExpressionForResource(
              codegenContext, resourceOrServiceShape, w)
          ),
          writer.consumer(w -> generateInterfaceOperationFunctionDefinitionForResource(
              codegenContext, resourceOrServiceShape, w)
          )
      );

      // Write implementation
      writer.write("""
        class $L(I$L):
            # TODO: typehint
            _impl: Any
            
            def __init__(self, _impl):
                self._impl = _impl
                
            ${C|}
        """,
          resourceOrServiceShape.getId().getName(),
          resourceOrServiceShape.getId().getName(),
          writer.consumer(w -> generateSmithyOperationFunctionDefinitionForResource(
              codegenContext, resourceOrServiceShape, w)
          )
      );
    }
  }

  private void generateInterfaceSubclasshookExpressionForResource(
      GenerationContext codegenContext, Shape resourceOrService, PythonWriter writer) {
    List<ShapeId> operationList = resourceOrService.asResourceShape().get().getOperations().stream().toList();
    Iterator<ShapeId> operationListIterator = operationList.iterator();

    // For all but the last operation shape, generate `hasattr and callable and`
    // For the last shape, generate `hasattr and callable`
    while (operationListIterator.hasNext()) {
      ShapeId operationShapeId = operationListIterator.next();
      writer.writeInline("""
          hasattr(subclass, "$L") and callable(subclass.$L)""",
          operationShapeId.getName(), operationShapeId.getName()
      );
      if (operationListIterator.hasNext()) {
        writer.write(" and");
      }
    }
  }

  private void generateInterfaceOperationFunctionDefinitionForResource(
      GenerationContext codegenContext, Shape resourceOrService, PythonWriter writer) {
    for (ShapeId operationShapeId : resourceOrService.asResourceShape().get().getOperations()) {
      writer.write("""
          @abc.abstractmethod
          def $L(self, dafny_input):
              raise NotImplementedError
          """, operationShapeId.getName());
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
