// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.util;

import java.util.function.BiConsumer;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.RequiredTrait;

public class TestModel {

  public static final String SERVICE_NAMESPACE = "test.foobar";
  public static final String SERVICE_NAME = "FoobarServiceFactory";
  public static final ShapeId SERVICE_SHAPE_ID = ShapeId.fromParts(
    SERVICE_NAMESPACE,
    SERVICE_NAME
  );

  /**
   * Sets up a test model. The updater can modify the {@link ServiceShape.Builder} or the {@link ModelAssembler}
   * before either is assembled. The updater is not responsible for adding the ServiceShape to the model assembler;
   * this method will do so before returning the assembled model.
   */
  public static Model setupModel(
    final BiConsumer<ServiceShape.Builder, ModelAssembler> updater
  ) {
    final ServiceShape.Builder serviceShapeBuilder = new ServiceShape.Builder()
      .version("1.0")
      .id(SERVICE_SHAPE_ID);
    final ModelAssembler assembler = new ModelAssembler();
    ModelUtils.addCustomTraitsToModelAssembler(assembler);

    updater.accept(serviceShapeBuilder, assembler);
    assembler.addShape(serviceShapeBuilder.build());
    return assembler.assemble().unwrap();
  }

  /**
   * Sets up a test model containing only the service shape.
   */
  public static Model setupModel() {
    return setupModel(
      (ServiceShape.Builder _builder, ModelAssembler _assembler) -> {}
    );
  }

  /**
   * Sets up a simple "Foobar" structure shape.
   */
  public static StructureShape setupFoobarStructureShape() {
    return StructureShape
      .builder()
      .id(ShapeId.fromParts(SERVICE_NAMESPACE, "Foobar"))
      .addMember("someInt", ShapeId.from("smithy.api#Integer"))
      .addMember("someString", ShapeId.from("smithy.api#String"))
      .addMember(
        "someBool",
        ShapeId.from("smithy.api#Boolean"),
        memberUpdater -> memberUpdater.addTrait(new RequiredTrait())
      )
      .build();
  }
}
