// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.traits;

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

import java.util.Optional;

/**
 * A trait that configures code generation for the creation of the client that provides the modeled API.
 * 'sdkId' is the name for the client that vends the API.
 * 'config' is the structure that customers provide to construct the client.
 */
public class LocalServiceTrait extends AbstractTrait implements ToSmithyBuilder<LocalServiceTrait> {
    public static final ShapeId ID = ShapeId.from("aws.polymorph#localService");

    private static final String SDKID = "sdkId";
    private static final String CONFIG = "config";
    private final String sdkId;
    private final ShapeId configId;

    private LocalServiceTrait(Builder builder) {
        super(ID, builder.getSourceLocation());
        this.sdkId = builder.sdkId;
        this.configId = builder.configId;
    }

    public static final class Provider extends AbstractTrait.Provider {
        public Provider() { super(ID); }

        @Override
        public Trait createTrait(ShapeId target, Node value) {
            ObjectNode objectNode = value.expectObjectNode();
            ShapeId configId = objectNode.getStringMember(CONFIG).map(StringNode::expectShapeId).get();
            String sdkId = objectNode.getStringMember(SDKID).get().toString();

            return builder()
              .sdkId(sdkId)
              .configId(configId)
              .build();
        }
    }

    public static Builder builder() { return new Builder(); }

    public String getSdkId() {
        return sdkId;
    }
    public ShapeId getConfigId() {
        return configId;
    }

    @Override
    protected Node createNode() {
        return Node
          .objectNodeBuilder()
          .sourceLocation(getSourceLocation())
          .withMember(this.sdkId, this.configId.toString())
          .build();
    }

    @Override
    public SmithyBuilder<LocalServiceTrait> toBuilder() {
        return builder()
          .sourceLocation(getSourceLocation())
          .sdkId(this.getSdkId())
          .configId(this.getConfigId());
    }

    /** Builder for {@link LocalServiceTrait}. */
    public static final class Builder extends AbstractTraitBuilder<LocalServiceTrait, Builder> {
        private String sdkId;
        private ShapeId configId;

        private Builder() {}

        @Override
        public LocalServiceTrait build() { return new LocalServiceTrait(this); }

        public LocalServiceTrait.Builder sdkId(String sdkId) {
            this.sdkId = sdkId;
            return this;
        }

        public LocalServiceTrait.Builder configId(ShapeId configId) {
            this.configId = configId;
            return this;
        }
    }

    public static Shape getDefinition() {
        final Trait localServiceTraitDefinition = TraitDefinition.builder()
                .selector(Selector.parse("service"))
                .build();
        return StructureShape.builder()
          .id(LocalServiceTrait.ID)
          .addTrait(localServiceTraitDefinition)
          .addMember("sdkId", ShapeId.from("smithy.api#String"))
          .addMember("config", ShapeId.from("smithy.api#String"))
          .build();
    }
}
