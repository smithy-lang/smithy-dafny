// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.traits;

import software.amazon.smithy.model.node.Node;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.AbstractTrait;
import software.amazon.smithy.model.traits.AbstractTraitBuilder;
import software.amazon.smithy.model.traits.Trait;
import software.amazon.smithy.utils.SmithyBuilder;
import software.amazon.smithy.utils.ToSmithyBuilder;

/**
 * A trait that signals that a service is a wrapped LocalService. This trait should NOT be added to
 * Smithy model files; it is intended to ONLY be added at runtime by Polymorph code generators that
 * implement SmithyBuildPlugins to signal that the code generation process should generate a wrapped
 * LocalService.
 */
public class WrappedLocalServiceTrait
  extends AbstractTrait
  implements ToSmithyBuilder<WrappedLocalServiceTrait> {

  public static final ShapeId ID = ShapeId.from(
    "aws.polymorph#wrappedLocalService"
  );

  private WrappedLocalServiceTrait(WrappedLocalServiceTrait.Builder builder) {
    super(ID, builder.getSourceLocation());
  }

  public static WrappedLocalServiceTrait.Builder builder() {
    return new WrappedLocalServiceTrait.Builder();
  }

  public static Shape getDefinition() {
    return StructureShape.builder().id(WrappedLocalServiceTrait.ID).build();
  }

  @Override
  protected Node createNode() {
    return Node.objectNodeBuilder().sourceLocation(getSourceLocation()).build();
  }

  @Override
  public SmithyBuilder<WrappedLocalServiceTrait> toBuilder() {
    return builder().sourceLocation(getSourceLocation());
  }

  public static final class Provider extends AbstractTrait.Provider {

    public Provider() {
      super(ID);
    }

    @Override
    public Trait createTrait(ShapeId target, Node value) {
      return builder().build();
    }
  }

  /** Builder for {@link WrappedLocalServiceTrait}. */
  public static final class Builder
    extends AbstractTraitBuilder<
      WrappedLocalServiceTrait,
      WrappedLocalServiceTrait.Builder
    > {

    private Builder() {}

    @Override
    public WrappedLocalServiceTrait build() {
      return new WrappedLocalServiceTrait(this);
    }
  }
}
