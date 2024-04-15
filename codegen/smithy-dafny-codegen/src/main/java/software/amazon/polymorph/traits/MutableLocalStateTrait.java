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
 * A tait the identifies that a resource caries mutable state.
 * This is useful for API consumers because they can reason about resources.
 * But this is critical for building Dafny components.
 * Since Dafny requires proving modifications are correct,
 * Polymorph needs to be able to integrate these mutations
 * with the History DafnyCallEvents.
 */
public class MutableLocalStateTrait
  extends AbstractTrait
  implements ToSmithyBuilder<MutableLocalStateTrait> {

  public static final ShapeId ID = ShapeId.from(
    "aws.polymorph#mutableLocalState"
  );

  private MutableLocalStateTrait(MutableLocalStateTrait.Builder builder) {
    super(ID, builder.getSourceLocation());
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

  public static MutableLocalStateTrait.Builder builder() {
    return new MutableLocalStateTrait.Builder();
  }

  @Override
  protected Node createNode() {
    return Node.objectNodeBuilder().sourceLocation(getSourceLocation()).build();
  }

  @Override
  public SmithyBuilder<MutableLocalStateTrait> toBuilder() {
    return builder().sourceLocation(getSourceLocation());
  }

  /** Builder for {@link MutableLocalStateTrait}. */
  public static final class Builder
    extends AbstractTraitBuilder<
      MutableLocalStateTrait,
      MutableLocalStateTrait.Builder
    > {

    private Builder() {}

    @Override
    public MutableLocalStateTrait build() {
      return new MutableLocalStateTrait(this);
    }
  }

  public static Shape getDefinition() {
    final Trait mutableLocalStateDefinition = TraitDefinition
      .builder()
      .selector(Selector.parse("resource"))
      .build();
    return StructureShape
      .builder()
      .id(MutableLocalStateTrait.ID)
      .addTrait(mutableLocalStateDefinition)
      .build();
  }
}
