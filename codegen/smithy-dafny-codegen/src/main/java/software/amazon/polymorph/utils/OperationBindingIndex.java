package software.amazon.polymorph.utils;

import java.util.Collections;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.stream.Collectors;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.knowledge.KnowledgeIndex;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ToShapeId;
import software.amazon.smithy.utils.SetUtils;

public class OperationBindingIndex implements KnowledgeIndex {

  private final Model model;
  private final Set<Shape> bindingShapes = new HashSet<>();
  private final Map<ShapeId, Set<Shape>> bindingShapesForOperation =
    new HashMap();
  private final Map<ShapeId, Set<BoundOperationShape>> operationBindings =
    new HashMap();

  public OperationBindingIndex(Model model) {
    this.model = model;

    for (final ServiceShape service : model.getServiceShapes()) {
      bindingShapes.add(service);
      for (final ShapeId operationId : service.getOperations()) {
        final OperationShape operationShape = model.expectShape(
          operationId,
          OperationShape.class
        );
        operationBindings
          .computeIfAbsent(service.getId(), id -> new HashSet<>())
          .add(new BoundOperationShape(service, operationShape));
        bindingShapesForOperation
          .computeIfAbsent(operationId, id -> new HashSet<>())
          .add(service);
      }
    }

    for (final ResourceShape resource : model.getResourceShapes()) {
      bindingShapes.add(resource);
      for (final ShapeId operationId : resource.getOperations()) {
        final OperationShape operationShape = model.expectShape(
          operationId,
          OperationShape.class
        );
        operationBindings
          .computeIfAbsent(resource.getId(), id -> new HashSet<>())
          .add(new BoundOperationShape(resource, operationShape));
        bindingShapesForOperation
          .computeIfAbsent(operationId, id -> new HashSet<>())
          .add(resource);
      }
    }
  }

  public Set<Shape> getAllBindingShapes() {
    return SetUtils.copyOf(bindingShapes);
  }

  public Set<Shape> getBindingShapes(ToShapeId operation) {
    return SetUtils.copyOf(
      bindingShapesForOperation.getOrDefault(
        operation.toShapeId(),
        Collections.emptySet()
      )
    );
  }

  public Set<BoundOperationShape> getBoundOperations(ToShapeId operation) {
    return getBindingShapes(operation)
      .stream()
      .map(bindingShape ->
        new BoundOperationShape(
          bindingShape,
          model.expectShape(operation.toShapeId(), OperationShape.class)
        )
      )
      .collect(Collectors.toSet());
  }

  public Set<BoundOperationShape> getOperations(ToShapeId bindingShape) {
    return SetUtils.copyOf(
      operationBindings.getOrDefault(
        bindingShape.toShapeId(),
        Collections.emptySet()
      )
    );
  }
}
