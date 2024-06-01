// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.traits;

import software.amazon.smithy.model.node.Node;
import software.amazon.smithy.model.selector.Selector;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.AbstractTrait;
import software.amazon.smithy.model.traits.AbstractTraitBuilder;
import software.amazon.smithy.model.traits.Trait;
import software.amazon.smithy.model.traits.TraitDefinition;
import software.amazon.smithy.utils.SmithyBuilder;
import software.amazon.smithy.utils.ToSmithyBuilder;

// TODO: Add parameters that are the order of the positional parameters.

/**
 * A trait representing that a structure should be "unwrapped" to its member whenever it is referenced.
 */
public class PositionalTrait
  extends AbstractTrait
  implements ToSmithyBuilder<PositionalTrait> {

  public static final ShapeId ID = ShapeId.from("aws.polymorph#positional");

  private PositionalTrait(Builder builder) {
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

  public static Builder builder() {
    return new Builder();
  }

  @Override
  protected Node createNode() {
    return Node.objectNodeBuilder().sourceLocation(getSourceLocation()).build();
  }

  @Override
  public SmithyBuilder<PositionalTrait> toBuilder() {
    return builder().sourceLocation(getSourceLocation());
  }

  /** Builder for {@link PositionalTrait}. */
  public static final class Builder
    extends AbstractTraitBuilder<PositionalTrait, Builder> {

    private Builder() {}

    @Override
    public PositionalTrait build() {
      return new PositionalTrait(this);
    }
  }

  public static Shape getDefinition() {
    final Trait positionalTraitDefinition = TraitDefinition
      .builder()
      .selector(Selector.parse("structure"))
      .build();
    return StructureShape
      .builder()
      .id(PositionalTrait.ID)
      .addTrait(positionalTraitDefinition)
      .build();
  }

  public static void validateUse(StructureShape shape) {
    if (!shape.hasTrait(PositionalTrait.class)) {
      return;
    }
    if (shape.members().size() == 1) {
      return;
    }
    String msg =
      "Structures with Positional Trait MUST have one and ONLY one member." +
      " Structure: %s".formatted(shape.getId());
    throw new IllegalArgumentException(msg);
  }

  public static MemberShape onlyMember(StructureShape shape) {
    validateUse(shape);
    // validateUse ensures there will be 1 member;
    // thus we know `Optional.get()` will succeed.
    //noinspection OptionalGetWithoutIsPresent
    return shape.members().stream().findFirst().get();
  }
}
