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
 * A trait representing a reference to either a service or resource, which we call the referent. A process holding such
 * a reference can invoke operations on the referent.
 */
public class ReferenceTrait
  extends AbstractTrait
  implements ToSmithyBuilder<ReferenceTrait> {

  public static final ShapeId ID = ShapeId.from("aws.polymorph#reference");

  private static final String SERVICE = "service";
  private static final String RESOURCE = "resource";

  private final ReferentType referentType;
  private final ShapeId referentId;

  private ReferenceTrait(Builder builder) {
    super(ID, builder.getSourceLocation());
    this.referentType = builder.referentType;
    this.referentId = builder.referentId;
  }

  public static final class Provider extends AbstractTrait.Provider {

    public Provider() {
      super(ID);
    }

    @Override
    public Trait createTrait(ShapeId target, Node value) {
      ObjectNode objectNode = value.expectObjectNode();
      Optional<ShapeId> serviceId = objectNode
        .getStringMember(SERVICE)
        .map(StringNode::expectShapeId);
      Optional<ShapeId> resourceId = objectNode
        .getStringMember(RESOURCE)
        .map(StringNode::expectShapeId);
      if (serviceId.isPresent() == resourceId.isPresent()) {
        throw new IllegalStateException(
          "Must specify either service or resource, but not both"
        );
      }
      ReferentType referentType = serviceId.isPresent()
        ? ReferentType.SERVICE
        : ReferentType.RESOURCE;
      ShapeId referentId = serviceId.orElseGet(resourceId::get);

      return builder()
        .referentType(referentType)
        .referentId(referentId)
        .build();
    }
  }

  public static Builder builder() {
    return new Builder();
  }

  public ReferentType getReferentType() {
    return referentType;
  }

  public boolean isService() {
    return referentType == ReferentType.SERVICE;
  }

  public ShapeId getReferentId() {
    return referentId;
  }

  public enum ReferentType {
    SERVICE,
    RESOURCE;

    @Override
    public String toString() {
      return switch (this) {
        case SERVICE -> ReferenceTrait.SERVICE;
        case RESOURCE -> ReferenceTrait.RESOURCE;
      };
    }

    public static ReferentType fromString(String referentTypeStr) {
      return switch (referentTypeStr) {
        case ReferenceTrait.SERVICE -> SERVICE;
        case ReferenceTrait.RESOURCE -> RESOURCE;
        default -> throw new UnsupportedOperationException();
      };
    }
  }

  @Override
  protected Node createNode() {
    return Node
      .objectNodeBuilder()
      .sourceLocation(getSourceLocation())
      .withMember(this.referentType.toString(), this.referentId.toString())
      .build();
  }

  @Override
  public SmithyBuilder<ReferenceTrait> toBuilder() {
    return builder()
      .sourceLocation(getSourceLocation())
      .referentType(this.getReferentType())
      .referentId(this.getReferentId());
  }

  /** Builder for {@link ReferenceTrait}. */
  public static final class Builder
    extends AbstractTraitBuilder<ReferenceTrait, Builder> {

    private ReferentType referentType;
    private ShapeId referentId;

    private Builder() {}

    @Override
    public ReferenceTrait build() {
      return new ReferenceTrait(this);
    }

    public Builder referentType(ReferentType referentType) {
      this.referentType = referentType;
      return this;
    }

    public Builder referentId(ShapeId referentId) {
      this.referentId = referentId;
      return this;
    }
  }

  public static Shape getDefinition() {
    final Trait referenceTraitDefinition = TraitDefinition
      .builder()
      .selector(Selector.parse("structure"))
      .build();
    return StructureShape
      .builder()
      .id(ReferenceTrait.ID)
      .addTrait(referenceTraitDefinition)
      .addMember("service", ShapeId.from("smithy.api#String"))
      .addMember("resource", ShapeId.from("smithy.api#String"))
      .build();
  }
}
