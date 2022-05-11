// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.utils;

import software.amazon.polymorph.traits.ClientConfigTrait;
import software.amazon.polymorph.traits.DafnyUtf8BytesTrait;
import software.amazon.polymorph.traits.ExtendableTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.loader.ModelAssembler;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.RequiredTrait;

import java.util.Optional;
import java.util.regex.Pattern;
import java.util.stream.Stream;

public class ModelUtils {
    // Require title-case alphanumeric names, so we don't need to check for keyword conflicts.
    //
    // The spec recommends a similar stricter definition for consistency (uppercase instead of title-case):
    // https://awslabs.github.io/smithy/1.0/spec/core/constraint-traits.html?highlight=enum#enum-trait
    private static final Pattern ENUM_NAME_PATTERN = Pattern.compile("^[A-Z]+[A-Za-z_0-9]*$");

    /**
     * Adds our custom traits (and their definitions) to a {@link ModelAssembler}.
     *
     * Note that this only needs to be called if the model file(s) being processed do not define these traits
     * (for example, in unit tests). If the model file does define the traits, adding them again does nothing.
     */
    public static void addCustomTraitsToModelAssembler(final ModelAssembler assembler) {
        assembler.addShape(ReferenceTrait.getDefinition());
        assembler.addShape(PositionalTrait.getDefinition());
        assembler.addShape(ClientConfigTrait.getDefinition());
        assembler.addShape(DafnyUtf8BytesTrait.getDefinition());
        assembler.addShape(ExtendableTrait.getDefinition());
    }

    /**
     * @return a stream of members of the given structure shape
     */
    public static Stream<MemberShape> streamStructureMembers(final StructureShape structureShape) {
        return structureShape.getAllMembers().values().stream();
    }

    /**
     * @return a stream of error structures in the given service shape
     */
    public static Stream<StructureShape> streamServiceErrors(final Model model, final ServiceShape serviceShape) {
        return model.getStructureShapesWithTrait(ErrorTrait.class)
                .stream()
                .filter(structureShape -> isInServiceNamespace(structureShape.getId(), serviceShape));
    }

    /**
     * @return true if the given shape ID is in the given service's namespace
     */
    public static boolean isInServiceNamespace(final ShapeId shapeId, final ServiceShape serviceShape) {
        return shapeId.getNamespace().equals(serviceShape.getId().getNamespace());
    }

    /**
     * Returns the sole member of the given positional structure shape, or {@link Optional#empty()} if the given shape
     * isn't a positional structure.
     */
    public static Optional<ShapeId> getPositionalStructureMember(final Shape shape) {
        if (!shape.hasTrait(PositionalTrait.class)) {
            return Optional.empty();
        }

        if (shape.members().size() != 1) {
            // For now, we only intend this trait to be used for operation returns, so we therefore only allow one
            // member. Eventually if we also want to use this to unwrap operation inputs (or any more general
            // unwrapping) we'll need to relax this constraint.
            throw new IllegalStateException("Structures marked with '@positional' must have exactly one member");
        }

        //noinspection OptionalGetWithoutIsPresent
        final MemberShape memberShape = shape.members()
                .stream()
                .findFirst()
                .get();
        return Optional.of(memberShape.getId());
    }

    public static boolean memberShapeIsOptional(final Model model, final MemberShape memberShape) {
        final Shape containerShape = model.expectShape(memberShape.getContainer());
        return containerShape.isStructureShape()
                && !containerShape.hasTrait(PositionalTrait.class)
                && !memberShape.isRequired();
    }

    /**
     * Returns true if the given shape ID is in the {@code smithy.api} namespace, or false otherwise.
     */
    public static boolean isSmithyApiShape(final ShapeId shapeId) {
        return shapeId.getNamespace().equals("smithy.api");
    }

    public static boolean isValidEnumDefinitionName(final String name) {
        return ENUM_NAME_PATTERN.matcher(name).matches();
    }

    /**
     * Like {@link ModelUtils#validateErrorStructureMessageNotRequired(StructureShape)} (StructureShape)}, but with the
     * added constraint that the {@code message} member must have the {@code @required} trait applied.
     */
    public static void validateErrorStructureMessageRequired(final StructureShape structureShape) {
        validateErrorStructureMessageNotRequired(structureShape);

        boolean messageRequired = structureShape.getMember("message")
                .filter(member -> member.hasTrait(RequiredTrait.class)).isPresent();
        if (!messageRequired) {
            throw new IllegalArgumentException("The 'message' member of %s must be @required"
                    .formatted(structureShape.getId()));
        }
    }

    /**
     * Throws {@link IllegalArgumentException} unless the given structure shape satisfies code-generation constraints:
     * <ul>
     *     <li>The structure must have the {@code @error} trait applied</li>
     *     <li>The structure must have a {@code message} member</li>
     *     <li>The structure must not have any members except {@code message}</li>
     * </ul>
     */
    public static void validateErrorStructureMessageNotRequired(final StructureShape structureShape) {
        if (!structureShape.hasTrait(ErrorTrait.class)) {
            throw new IllegalArgumentException("%s is not an @error structure".formatted(structureShape.getId()));
        }

        boolean hasMessage = structureShape.getMember("message").isPresent();
        if (!hasMessage) {
            throw new IllegalArgumentException("Error structure %s is missing a 'message' member"
                    .formatted(structureShape.getId()));
        }

        // TODO support other members
        if (structureShape.getMemberNames().size() > 1) {
            throw new IllegalArgumentException("Error structure %s cannot have members other than 'message'"
                    .formatted(structureShape.getId()));
        }
    }
}
