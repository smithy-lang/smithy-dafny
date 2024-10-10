package software.amazon.polymorph.utils;

import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.Shape;

public record BoundOperationShape(
  Shape bindingShape,
  OperationShape operationShape
) {}
