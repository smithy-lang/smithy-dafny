// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.traits;

import java.util.Optional;
import software.amazon.smithy.model.node.Node;
import software.amazon.smithy.model.node.ObjectNode;
import software.amazon.smithy.model.node.StringNode;
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
 * A trait indicating the structure that should be used as the client configuration object when generating the client
 * code for a service structure.
 */
public class ClientConfigTrait
  extends AbstractTrait
  implements ToSmithyBuilder<ClientConfigTrait> {

  public static final ShapeId ID = ShapeId.from("aws.polymorph#clientConfig");

  private final ShapeId clientConfigId;

  private static final String CONFIG = "config";

  private ClientConfigTrait(Builder builder) {
    super(ID, builder.getSourceLocation());
    this.clientConfigId = builder.clientConfigId;
  }

  public static final class Provider extends AbstractTrait.Provider {

    public Provider() {
      super(ID);
    }

    @Override
    public Trait createTrait(ShapeId target, Node value) {
      ObjectNode objectNode = value.expectObjectNode();
      Optional<ShapeId> configIdOptional = objectNode
        .getStringMember(CONFIG)
        .map(StringNode::expectShapeId);
      ShapeId configId = configIdOptional.orElseThrow(() ->
        new IllegalStateException("Must specify a config")
      );

      return builder().clientConfigId(configId).build();
    }
  }

  public static Builder builder() {
    return new Builder();
  }

  public ShapeId getClientConfigId() {
    return this.clientConfigId;
  }

  @Override
  protected Node createNode() {
    return Node
      .objectNodeBuilder()
      .sourceLocation(getSourceLocation())
      .withMember(CONFIG, this.clientConfigId.toString())
      .build();
  }

  @Override
  public SmithyBuilder<ClientConfigTrait> toBuilder() {
    return builder().sourceLocation(getSourceLocation());
  }

  /** Builder for {@link ClientConfigTrait}. */
  public static final class Builder
    extends AbstractTraitBuilder<ClientConfigTrait, Builder> {

    private ShapeId clientConfigId;

    private Builder() {}

    @Override
    public ClientConfigTrait build() {
      return new ClientConfigTrait(this);
    }

    public Builder clientConfigId(ShapeId clientConfigId) {
      this.clientConfigId = clientConfigId;
      return this;
    }
  }

  public static Shape getDefinition() {
    final Trait clientConfigTraitDefinition = TraitDefinition
      .builder()
      .selector(Selector.parse("service"))
      .build();
    return StructureShape
      .builder()
      .id(ClientConfigTrait.ID)
      .addTrait(clientConfigTraitDefinition)
      .addMember(CONFIG, ShapeId.from("smithy.api#String"))
      .build();
  }
}
