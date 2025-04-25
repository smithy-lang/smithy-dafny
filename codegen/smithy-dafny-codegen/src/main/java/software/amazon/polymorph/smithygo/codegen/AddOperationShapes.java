/*
 * Copyright 2020 Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

package software.amazon.polymorph.smithygo.codegen;

import java.util.TreeSet;
import java.util.logging.Logger;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.knowledge.TopDownIndex;
import software.amazon.smithy.model.shapes.AbstractShapeBuilder;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;

/**
 * Ensures that each operation has a unique input and output shape.
 */
public final class AddOperationShapes {

  private static final Logger LOGGER = Logger.getLogger(
    AddOperationShapes.class.getName()
  );

  private AddOperationShapes() {}

  /**
   * Processes the given model and returns a new model ensuring service operation has an unique input and output
   * synthesized shape.
   *
   * @param model          the model
   * @param serviceShapeId the service shape
   * @return a model with unique operation input and output shapes
   */
  public static Model execute(Model model, ShapeId serviceShapeId) {
    TopDownIndex topDownIndex = model.getKnowledge(TopDownIndex.class);
    ServiceShape service = model.expectShape(
      serviceShapeId,
      ServiceShape.class
    );
    TreeSet<OperationShape> operations = new TreeSet<>(
      topDownIndex.getContainedOperations(model.expectShape(serviceShapeId))
    );

    Model.Builder modelBuilder = model.toBuilder();
    for (OperationShape operation : operations) {
      OperationShape.Builder operationBuilder = operation.toBuilder();
      ShapeId operationId = operation.getId();
      LOGGER.info(() -> "building unique input/output shapes for " + operationId
      );
      if (operation.getInput().isPresent()) {
        StructureShape newInputShape = operation
          .getInput()
          .map(shapeId ->
            cloneOperationShape(
              service,
              operationId,
              (StructureShape) model.expectShape(shapeId),
              "Input"
            )
          )
          .get();
        modelBuilder.addShape(newInputShape);
        operationBuilder.input(newInputShape.toShapeId());
      }

      if (operation.getOutput().isPresent()) {
        StructureShape newOutputShape = operation
          .getOutput()
          .map(shapeId ->
            cloneOperationShape(
              service,
              operationId,
              (StructureShape) model.expectShape(shapeId),
              "Output"
            )
          )
          .get();
        modelBuilder.addShape(newOutputShape);
        operationBuilder.output(newOutputShape.toShapeId());
      }

      // Update operation model with the input/output shape ids
      modelBuilder.addShape(operationBuilder.build());
    }

    return modelBuilder.build();
  }

  private static StructureShape cloneOperationShape(
    ServiceShape service,
    ShapeId operationShapeId,
    StructureShape structureShape,
    String suffix
  ) {
    return (StructureShape) cloneShape(
      structureShape,
      operationShapeId.getName(service) + suffix
    );
  }

  private static Shape cloneShape(Shape shape, String cloneShapeName) {
    ShapeId cloneShapeId = ShapeId.fromParts(
      shape.toShapeId().getNamespace(),
      cloneShapeName
    );

    AbstractShapeBuilder builder = Shape
      .shapeToBuilder(shape)
      .id(cloneShapeId)
      .addTrait(Synthetic.builder().archetype(shape.getId()).build());

    shape
      .members()
      .forEach(memberShape -> {
        builder.addMember(
          memberShape
            .toBuilder()
            .id(cloneShapeId.withMember(memberShape.getMemberName()))
            .build()
        );
      });

    return (Shape) builder.build();
  }
}
