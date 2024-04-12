// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.traits;

import java.util.LinkedHashSet;
import java.util.Objects;
import java.util.Optional;
import java.util.stream.Collectors;
import java.util.stream.Stream;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import software.amazon.smithy.model.node.ArrayNode;
import software.amazon.smithy.model.node.Node;
import software.amazon.smithy.model.node.ObjectNode;
import software.amazon.smithy.model.node.StringNode;
import software.amazon.smithy.model.selector.Selector;
import software.amazon.smithy.model.shapes.ListShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.AbstractTrait;
import software.amazon.smithy.model.traits.AbstractTraitBuilder;
import software.amazon.smithy.model.traits.IdRefTrait;
import software.amazon.smithy.model.traits.RequiredTrait;
import software.amazon.smithy.model.traits.Trait;
import software.amazon.smithy.model.traits.TraitDefinition;
import software.amazon.smithy.utils.SmithyBuilder;
import software.amazon.smithy.utils.ToSmithyBuilder;

/**
 * A trait that configures code generation for the creation of the client that provides the modeled API.
 * 'sdkId' is the name for the client that vends the API.
 * 'config' is the structure that customers provide to construct the client.
 * 'dependencies' is an optional list of services that the target service depends on.
 */
public class LocalServiceTrait
  extends AbstractTrait
  implements ToSmithyBuilder<LocalServiceTrait> {

  public static final String NAMESPACE = "aws.polymorph";
  public static final ShapeId LOCAL_SERVICE_ID = ShapeId.fromParts(
    NAMESPACE,
    "localService"
  );
  public static final ShapeId SERVICE_LIST_ID = ShapeId.fromParts(
    NAMESPACE,
    "ServiceList"
  );

  protected static final String SDKID = "sdkId";
  protected static final String CONFIG = "config";
  private static final String DEPENDENCIES = "dependencies";

  @Nonnull
  private final String sdkId;

  @Nonnull
  private final ShapeId configId;

  @Nullable
  private final LinkedHashSet<ShapeId> dependencies;

  private LocalServiceTrait(Builder builder) {
    super(LOCAL_SERVICE_ID, builder.getSourceLocation());
    this.sdkId = builder.sdkId;
    this.configId = builder.configId;
    this.dependencies = builder.dependencies;
  }

  public static final class Provider extends AbstractTrait.Provider {

    public Provider() {
      super(LOCAL_SERVICE_ID);
    }

    @Override
    public Trait createTrait(ShapeId target, Node value) {
      ObjectNode objectNode = value.expectObjectNode();
      ShapeId configId = objectNode.expectStringMember(CONFIG).expectShapeId();
      String sdkId = objectNode.expectStringMember(SDKID).toString();
      Optional<ArrayNode> maybeRawDependencies = objectNode.getArrayMember(
        DEPENDENCIES
      );
      Builder builder = builder();
      if (maybeRawDependencies.isPresent()) {
        ArrayNode rawDependencies = maybeRawDependencies.get();
        final LinkedHashSet<ShapeId> dependencies = rawDependencies
          .getElementsAs(StringNode.class)
          .stream()
          .map(StringNode::expectShapeId)
          .collect(Collectors.toCollection(LinkedHashSet::new));
        builder.dependencies(dependencies);
      }

      return builder.sdkId(sdkId).configId(configId).build();
    }
  }

  public static Builder builder() {
    return new Builder();
  }

  @Nonnull
  public String getSdkId() {
    return sdkId;
  }

  @Nonnull
  public ShapeId getConfigId() {
    return configId;
  }

  @Nullable
  public LinkedHashSet<ShapeId> getDependencies() {
    return dependencies;
  }

  @Override
  protected Node createNode() {
    return Node
      .objectNodeBuilder()
      .sourceLocation(getSourceLocation())
      .withMember(SDKID, this.sdkId)
      .withMember(CONFIG, this.configId.toString())
      .withOptionalMember(
        DEPENDENCIES,
        Optional.ofNullable(dependenciesAsArrayNode())
      )
      .build();
  }

  @Nullable
  protected ArrayNode dependenciesAsArrayNode() {
    if (Objects.isNull(this.dependencies)) {
      return null;
    }
    final ArrayNode.Builder builder = ArrayNode.builder();
    dependencies.stream().map(ShapeId::toString).forEach(builder::withValue);
    return builder.build();
  }

  @Override
  public SmithyBuilder<LocalServiceTrait> toBuilder() {
    return builder()
      .sourceLocation(getSourceLocation())
      .sdkId(this.getSdkId())
      .configId(this.getConfigId())
      .dependencies(this.getDependencies());
  }

  /** Builder for {@link LocalServiceTrait}. */
  public static final class Builder
    extends AbstractTraitBuilder<LocalServiceTrait, Builder> {

    private String sdkId;
    private ShapeId configId;
    private LinkedHashSet<ShapeId> dependencies;

    private Builder() {}

    @Override
    public LocalServiceTrait build() {
      return new LocalServiceTrait(this);
    }

    public LocalServiceTrait.Builder sdkId(String sdkId) {
      this.sdkId = sdkId;
      return this;
    }

    public LocalServiceTrait.Builder configId(ShapeId configId) {
      this.configId = configId;
      return this;
    }

    public LocalServiceTrait.Builder dependencies(
      LinkedHashSet<ShapeId> dependencies
    ) {
      this.dependencies = dependencies;
      return this;
    }
  }

  public static Stream<Shape> getDefinitions() {
    final MemberShape serviceMember = MemberShape
      .builder()
      .id(
        ShapeId.fromParts(
          SERVICE_LIST_ID.getNamespace(),
          SERVICE_LIST_ID.getName(),
          "member"
        )
      )
      .addTrait(
        IdRefTrait
          .builder()
          .selector(Selector.parse("service"))
          .failWhenMissing(true)
          .build()
      )
      .target("smithy.api#String")
      .build();
    final ListShape serviceListShape = ListShape
      .builder()
      .id(LocalServiceTrait.SERVICE_LIST_ID)
      .member(serviceMember)
      .build();
    final MemberShape skidShape = MemberShape
      .builder()
      .addTrait(new RequiredTrait())
      .id(
        ShapeId.fromParts(
          LOCAL_SERVICE_ID.getNamespace(),
          LOCAL_SERVICE_ID.getName(),
          SDKID
        )
      )
      .target("smithy.api#String")
      .build();
    final MemberShape configShape = MemberShape
      .builder()
      .addTrait(new RequiredTrait())
      .addTrait(
        IdRefTrait
          .builder()
          .selector(Selector.parse("structure"))
          .failWhenMissing(true)
          .build()
      )
      .id(
        ShapeId.fromParts(
          LOCAL_SERVICE_ID.getNamespace(),
          LOCAL_SERVICE_ID.getName(),
          CONFIG
        )
      )
      .target("smithy.api#String")
      .build();
    final Trait localServiceTraitDefinition = TraitDefinition
      .builder()
      .selector(Selector.parse("service"))
      .build();
    final StructureShape localService = StructureShape
      .builder()
      .id(LocalServiceTrait.LOCAL_SERVICE_ID)
      .addTrait(localServiceTraitDefinition)
      .addMember(skidShape)
      .addMember(configShape)
      .addMember(DEPENDENCIES, LocalServiceTrait.SERVICE_LIST_ID)
      .build();
    return Stream.of(serviceListShape, localService);
  }
}
