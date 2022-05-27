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
 * A trait indicating the structure is *only* used in a union.
 * // A trait indicating that a structure is a members of a union
 * // and MUST NOT be used independently of the union.
 * // This is syntactic sugar for
 * //  union Foo {
 * //    Bar: structure Bar { baz: String }
 * //  }
 * //
 * // It is used like this
 * //  union Foo {
 * //    Bar: Bar
 * //  }
 * //  structure Bar { baz: String }
 * // This is especially useful in Dafny.
 * // Because it results in a single datatype
 * // who's constructors are the member structures.
 * // datatypes Foo = Bar( baz: String )
 */
public class DataTypeUnionTrait extends AbstractTrait implements ToSmithyBuilder<DataTypeUnionTrait> {
    public static final ShapeId ID = ShapeId.from("aws.polymorph#datatypeUnion");

    private DataTypeUnionTrait(Builder builder) { super(ID, builder.getSourceLocation()); }

    public static final class Provider extends AbstractTrait.Provider {
        public Provider() { super(ID); }

        @Override
        public Trait createTrait(ShapeId target, Node value) { return new Builder().build(); }
    }

    public static Builder builder() { return new Builder(); }

    @Override
    protected Node createNode() {
        return Node.objectNodeBuilder()
                .sourceLocation(getSourceLocation())
                .build();
    }

    @Override
    public SmithyBuilder<DataTypeUnionTrait> toBuilder() {
        return builder().sourceLocation(getSourceLocation());
    }

    /** Builder for {@link DataTypeUnionTrait}. */
    public static final class Builder extends AbstractTraitBuilder<DataTypeUnionTrait, Builder> {

        private Builder() {}

        @Override
        public DataTypeUnionTrait build() { return new DataTypeUnionTrait(this); }
    }

    public static Shape getDefinition() {
        final Trait datatypeUnionTraitDefinition = TraitDefinition.builder()
                .selector(Selector.parse("structure"))
                .build();
        return StructureShape.builder()
                .id(DataTypeUnionTrait.ID)
                .addTrait(datatypeUnionTraitDefinition)
                .build();
    }
}
