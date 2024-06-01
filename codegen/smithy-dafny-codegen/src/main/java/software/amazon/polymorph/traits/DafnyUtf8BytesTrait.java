// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.traits;

import software.amazon.smithy.model.node.Node;
import software.amazon.smithy.model.node.ObjectNode;
import software.amazon.smithy.model.selector.Selector;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.AnnotationTrait;
import software.amazon.smithy.model.traits.Trait;
import software.amazon.smithy.model.traits.TraitDefinition;

/**
 * Indicates that a string is represented as a sequence of UTF-8 encoded bytes in Dafny, rather than the default
 * sequence of UTF-16 chars.
 * <p>
 * This trait is a workaround. Smithy "string" types represent UTF-8, but Dafny and C# natively use UTF-16 as the
 * primary char and string primitive types. So normally, generated/compiled Dafny and C# code would just use UTF-16 to
 * represent string types. But the Dafny implementation (and generated API) use explicit UTF-8 byte arrays where doing
 * so makes verification easier. So we need this mechanism in the model to tell codegen which Dafny representation will
 * be used: sequences of UTF-16 chars or UTF-8 bytes.
 * <p>
 * The current plan is to change the definition of string in Dafny 4.0 to support Unicode in general better. When that
 * lands we should be able to make the necessary changes to clean this up in the codegen/model without affecting any
 * customers (who WILL be using their idiomatic representation of strings).
 * <p>
 * See: <a href="https://github.com/dafny-lang/dafny/issues/413">dafny-lang/dafny#413: Revisit definition of Dafny strings</a>
 */
// TODO: remove this trait
public final class DafnyUtf8BytesTrait extends AnnotationTrait {

  public static final ShapeId ID = ShapeId.from("aws.polymorph#dafnyUtf8Bytes");

  public DafnyUtf8BytesTrait(ObjectNode node) {
    super(ID, node);
  }

  public DafnyUtf8BytesTrait() {
    this(Node.objectNode());
  }

  public static final class Provider
    extends AnnotationTrait.Provider<DafnyUtf8BytesTrait> {

    public Provider() {
      super(ID, DafnyUtf8BytesTrait::new);
    }
  }

  public static Shape getDefinition() {
    final Trait traitDefinition = TraitDefinition
      .builder()
      .selector(Selector.parse("string"))
      .build();
    return StructureShape
      .builder()
      .id(DafnyUtf8BytesTrait.ID)
      .addTrait(traitDefinition)
      .build();
  }
}
