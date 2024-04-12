// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.traits;

import software.amazon.smithy.model.node.Node;
import software.amazon.smithy.model.selector.Selector;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.AbstractTrait;
import software.amazon.smithy.model.traits.AbstractTraitBuilder;
import software.amazon.smithy.model.traits.Trait;
import software.amazon.smithy.model.traits.TraitDefinition;
import software.amazon.smithy.utils.SmithyBuilder;
import software.amazon.smithy.utils.ToSmithyBuilder;

/**
 * A trait indicating the resource is extendable.
 * i.e.: Users may author their own classes that implement and extend this resource.
 */
public class ExtendableTrait
  extends AbstractTrait
  implements ToSmithyBuilder<ExtendableTrait> {

  public static final ShapeId ID = ShapeId.from("aws.polymorph#extendable");

  private ExtendableTrait(Builder builder) {
    super(ID, builder.getSourceLocation());
  }

  public static final class Provider extends AbstractTrait.Provider {

    public Provider() {
      super(ID);
    }

    @Override
    public Trait createTrait(ShapeId target, Node value) {
      return new Builder().build();
    }
  }

  public static Builder builder() {
    return new Builder();
  }

  @Override
  protected Node createNode() {
    return Node.objectNodeBuilder().sourceLocation(getSourceLocation()).build();
  }

  @Override
  public SmithyBuilder<ExtendableTrait> toBuilder() {
    return builder().sourceLocation(getSourceLocation());
  }

  /** Builder for {@link ExtendableTrait}. */
  public static final class Builder
    extends AbstractTraitBuilder<ExtendableTrait, Builder> {

    private Builder() {}

    @Override
    public ExtendableTrait build() {
      return new ExtendableTrait(this);
    }
  }

  public static Shape getDefinition() {
    final Trait extendableTraitDefinition = TraitDefinition
      .builder()
      .selector(Selector.parse("resource"))
      .build();
    return StructureShape
      .builder()
      .id(ExtendableTrait.ID)
      .addTrait(extendableTraitDefinition)
      .build();
  }
}
