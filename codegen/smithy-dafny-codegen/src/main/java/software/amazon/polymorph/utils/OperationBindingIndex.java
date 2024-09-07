package software.amazon.polymorph.utils;

import software.amazon.smithy.model.knowledge.KnowledgeIndex;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ToShapeId;

import java.util.HashMap;
import java.util.Map;
import java.util.Optional;

public class OperationBindingIndex implements KnowledgeIndex {
  private final Map<ShapeId, Shape> operationBindings = new HashMap();

  public OperationBindingIndex(Model model) {
    for (final ServiceShape service : model.getServiceShapes()) {
      for (final ShapeId operationId : service.getOperations()) {
        operationBindings.put(operationId, service);
      }
    }

    for (final ResourceShape resource : model.getResourceShapes()) {
      for (final ShapeId operationId : resource.getOperations()) {
        operationBindings.put(operationId, resource);
      }
    }
  }

  public Optional<Shape> getBindingShape(ToShapeId operation) {
    return Optional.ofNullable(operationBindings.get(operation.toShapeId()));
  }
}
