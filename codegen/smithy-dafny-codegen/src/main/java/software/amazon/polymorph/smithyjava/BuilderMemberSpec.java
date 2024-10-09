// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
package software.amazon.polymorph.smithyjava;

import static software.amazon.polymorph.smithyjava.generator.Generator.INTERFACE_VAR;
import static software.amazon.polymorph.utils.AwsSdkNameResolverHelpers.isInAwsSdkNamespace;
import static software.amazon.polymorph.utils.ModelUtils.resolveShape;

import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.FieldSpec;
import com.squareup.javapoet.TypeName;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import javax.annotation.Nonnull;
import javax.annotation.Nullable;
import javax.lang.model.element.Modifier;
import software.amazon.polymorph.smithyjava.generator.library.JavaLibrary;
import software.amazon.polymorph.smithyjava.nameresolver.Native;
import software.amazon.polymorph.smithyjava.unmodeled.CollectionOfErrors;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.ModelUtils.ResolvedShapeId;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.StructureShape;

// TODO: We can shrink our code base by combining
//  BuilderMemberSpec w/ PolymorphFieldSpec.
// They serve very similar purposes:
// Parsing Traits from Smithy Shapes for Builder Class generators.
public class BuilderMemberSpec {

  private static final BuilderMemberSpec _MESSAGE = new BuilderMemberSpec(
    TypeName.get(String.class),
    "message",
    "The detailed message. The detail message is saved for" +
    " later retrieval by the {@link #getMessage()} method."
  );
  private static final BuilderMemberSpec _CAUSE = new BuilderMemberSpec(
    TypeName.get(Throwable.class),
    "cause",
    "The cause (which is saved for later retrieval by the" +
    " {@link #getCause()} method). (A {@code null} value is" +
    " permitted, and indicates that the cause is nonexistent or" +
    " unknown.)"
  );
  public static final List<BuilderMemberSpec> THROWABLE_ARGS = List.of(
    _MESSAGE,
    _CAUSE
  );
  public static final List<BuilderMemberSpec> OPAQUE_ARGS = List.of(
    _MESSAGE,
    _CAUSE,
    new BuilderMemberSpec(
      TypeName.get(Object.class),
      "obj",
      "The unexpected object encountered. It MIGHT BE an Exception," +
      " but that is not guaranteed."
    ),
    new BuilderMemberSpec(
      TypeName.get(String.class),
      "altText",
      "A best effort text representation of obj."
    )
  );
  public static final List<BuilderMemberSpec> COLLECTION_ARGS = List.of(
    _MESSAGE,
    _CAUSE,
    new BuilderMemberSpec(
      CollectionOfErrors.exceptionList(),
      "list",
      "The list of Exceptions encountered."
    )
  );

  @Nonnull
  public final TypeName type;

  @Nonnull
  public final String name;

  @Nullable
  public final TypeName interfaceType;

  @Nullable
  public final CodeBlock wrapCall;

  @Nullable
  public final String javaDoc;

  public BuilderMemberSpec(MemberShape memberShape, JavaLibrary subject) {
    ResolvedShapeId resolvedShapeId = resolveShape(
      memberShape.getTarget(),
      subject.model
    );
    Shape resolvedShape = subject.model.expectShape(
      resolvedShapeId.resolvedId()
    );
    this.type =
      subject.nativeNameResolver.typeForShape(resolvedShapeId.naiveId());
    this.name = memberShape.getMemberName();
    if (
      (resolvedShape.isResourceShape()) &&
      !isInAwsSdkNamespace(resolvedShapeId.resolvedId())
    ) {
      // If target is a non-AWS Resource,
      // the output type should be an interface
      this.interfaceType =
        Native.classNameForInterfaceOrLocalService(
          resolvedShape,
          subject.sdkVersion
        );
      // And we will need to wrap it
      this.wrapCall =
        subject.wrapWithShim(
          resolvedShapeId.resolvedId(),
          CodeBlock.of(this.name)
        );
    } else {
      this.interfaceType = null;
      this.wrapCall = null;
    }
    this.javaDoc =
      ModelUtils
        .getDocumentationOrJavadoc(memberShape)
        .or(() -> ModelUtils.getDocumentationOrJavadoc(resolvedShape))
        .orElse(null);
  }

  /** Private Method for handling Edge Cases or cases where
   * the target shape cannot be a member shape. */
  private BuilderMemberSpec(
    @Nonnull TypeName type,
    @Nonnull String name,
    @Nullable String javaDoc
  ) {
    this.interfaceType = null;
    this.wrapCall = null;
    this.name = name;
    this.type = type;
    this.javaDoc = javaDoc;
  }

  /** A Local Service Shim is built with a Configuration object,
   *  which is stored as a field of the shim. */
  // TODO: Should the Config object be optional?
  public static BuilderMemberSpec localServiceConfigMemberSpec(
    LocalServiceTrait trait,
    JavaLibrary subject
  ) {
    TypeName type = subject.nativeNameResolver.typeForShape(
      trait.getConfigId()
    );
    String name = trait.getConfigId().getName();
    StructureShape structureShape = subject.model.expectShape(
      trait.getConfigId(),
      StructureShape.class
    );
    String javaDoc = ModelUtils
      .getDocumentationOrJavadoc(structureShape)
      .orElse(null);
    return new BuilderMemberSpec(type, name, javaDoc);
  }

  public static BuilderMemberSpec localServiceAsMemberSpec(
    JavaLibrary subject
  ) {
    TypeName type = subject.nativeNameResolver.classNameForService(
      subject.serviceShape
    );
    String name = INTERFACE_VAR;
    String javaDoc = ModelUtils
      .getDocumentationOrJavadoc(subject.serviceShape)
      .orElse(null);
    return new BuilderMemberSpec(type, name, javaDoc);
  }

  public FieldSpec toFieldSpec(@Nullable Modifier... modifiers) {
    FieldSpec.Builder fieldSpec = FieldSpec.builder(this.type, this.name);
    if (Objects.nonNull(modifiers)) {
      fieldSpec.addModifiers(modifiers);
    }
    if (Objects.nonNull(this.javaDoc)) {
      fieldSpec.addJavadoc(this.javaDoc);
    }
    return fieldSpec.build();
  }
}
