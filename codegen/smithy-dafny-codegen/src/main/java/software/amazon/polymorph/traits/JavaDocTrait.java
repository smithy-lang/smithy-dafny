// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.traits;

import software.amazon.smithy.model.SourceLocation;
import software.amazon.smithy.model.selector.Selector;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.traits.StringTrait;
import software.amazon.smithy.model.traits.Trait;
import software.amazon.smithy.model.traits.TraitDefinition;

public class JavaDocTrait extends StringTrait {

  public static final ShapeId ID = ShapeId.from("aws.polymorph#javadoc");

  public JavaDocTrait(String value, SourceLocation sourceLocation) {
    super(ID, value, sourceLocation);
  }

  public JavaDocTrait(String value) {
    this(value, SourceLocation.NONE);
  }

  public static final class Provider
    extends StringTrait.Provider<JavaDocTrait> {

    public Provider() {
      super(ID, JavaDocTrait::new);
    }
  }

  public static Shape getDefinition() {
    final Trait traitDefinition = TraitDefinition
      .builder()
      .selector(Selector.parse("*"))
      .build();
    return StringShape
      .builder()
      .id(JavaDocTrait.ID)
      .addTrait(traitDefinition)
      .build();
  }
}
