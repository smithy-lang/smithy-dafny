// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydafny;

import com.google.common.base.Joiner;

import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.ShapeType;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.utils.StringUtils;

import javax.annotation.Nullable;
import java.util.Arrays;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.stream.Stream;

public record DafnyNameResolver(Model model, ServiceShape serviceShape) {
    public static final Map<ShapeType, String> DAFNY_TYPES_BY_SIMPLE_SHAPE_TYPE = Map.ofEntries(
            Map.entry(ShapeType.BLOB, "seq<uint8>"),
            Map.entry(ShapeType.BOOLEAN, "bool"),
            Map.entry(ShapeType.STRING, "string"),
            // currently unused in model and unsupported in StandardLibrary.UInt
//            Map.entry(ShapeType.BYTE, "int8"),
//            Map.entry(ShapeType.SHORT, "int16"),
            Map.entry(ShapeType.INTEGER, "int32"),
            Map.entry(ShapeType.LONG, "int64")
    );

    public String nameForService(final ServiceShape serviceShape) {
        return StringUtils.capitalize(serviceShape.getContextualName(this.serviceShape));
    }

    public String nameForService() {
        return nameForService(serviceShape);
    }

    public String nameForServiceErrorConstructor(final ShapeId errorShapeId) {
        return "%1$s_%2$s".formatted(this.nameForService(), this.baseTypeForShape(errorShapeId));
    }

    @SuppressWarnings("OptionalGetWithoutIsPresent")
    public String baseTypeForShape(final ShapeId shapeId) {
        final Shape shape = model.expectShape(shapeId);
        final String shapeName = shapeId.getName(serviceShape);

        if (ModelUtils.isSmithyApiShape(shapeId)) {
            @Nullable final String simpleShapeType = DAFNY_TYPES_BY_SIMPLE_SHAPE_TYPE.get(shape.getType());
            return Objects.requireNonNull(simpleShapeType,
                    () -> String.format("No Dafny type for prelude shape %s", shapeId));
        }

        return switch (shape.getType()) {
            case BLOB, BOOLEAN, STRING,
                    // currently unused in model and unsupported in StandardLibrary.UInt
                    // BYTE, SHORT
                    INTEGER, LONG,
                    LIST, MAP, STRUCTURE -> shapeName;
            case SERVICE -> traitForServiceClient(shape.asServiceShape().get());
            case RESOURCE -> traitForResource(shape.asResourceShape().get());
            case MEMBER -> baseTypeForMember(shape.asMemberShape().get());
            // TODO create/use better timestamp type in Dafny libraries
            case TIMESTAMP -> "string";
            default -> throw new UnsupportedOperationException(
                    "Shape %s has unsupported type %s".formatted(shapeId, shape.getType()));
        };
    }

    private String baseTypeForMember(final MemberShape memberShape) {
        final Optional<ShapeId> referentId = Optional.of(memberShape.getTarget())
                    .flatMap(model::getShape)
                    .flatMap(targetShape -> targetShape.getTrait(ReferenceTrait.class))
                    .map(referenceTrait -> referenceTrait.getReferentId());
                            
        final String targetType = baseTypeForShape(referentId.orElse(memberShape.getTarget()));
        if (!ModelUtils.memberShapeIsOptional(model, memberShape)) {
            return targetType;
        }

        return ("Option<%s>").formatted(targetType);

    }

    public String generatedTypeForShape(final ShapeId shapeId) {
        return StringUtils.capitalize(shapeId.getName(serviceShape));
    }

    public String traitForServiceClient(final ServiceShape serviceShape) {
        return "I%sClient".formatted(nameForService(serviceShape));
    }

    public String traitForResource(final ResourceShape resourceShape) {
        final String resourceName = StringUtils.capitalize(resourceShape.getId().getName(this.serviceShape));
        return "I%s".formatted(resourceName);
    }

    public String traitForServiceError(final ServiceShape serviceShape) {
        return "I%sException".formatted(nameForService(serviceShape));
    }

    public String classForSpecificError(final StructureShape structureShape) {
        return StringUtils.capitalize(structureShape.getId().getName());
    }

    public String classForUnknownError(final ServiceShape serviceShape) {
        return "Unknown%sError".formatted(nameForService(serviceShape));
    }

    public String methodForOperation(final OperationShape operationShape) {
        return StringUtils.capitalize(operationShape.getId().getName(serviceShape));
    }

    public String predicateCalledWith(final OperationShape operationShape) {
        return "%sCalledWith".formatted(this.methodForOperation(operationShape));
    }

    /**
     * Returns the return type for an operation of this service.
     * This is {@code Result<T, errorType>},
     * where {@code T} is either...
     * <ul>
     *     <li>... the corresponding Dafny output type, if the operation has output.</li>
     *     <li>... {@code ()} ("unit"), if the operation does not have output.</li>
     * </ul>
     */
    public String returnTypeForOperation(final OperationShape operationShape) {
        final String outputType = operationShape.getOutput()
                .map(this::baseTypeForShape)
                .orElse("()");
        return "Result<%s, %s>".formatted(outputType, traitForServiceError(serviceShape));
    }

    public Optional<String> returnTypeForResult(final OperationShape operationShape) {
        if (operationShape.getOutput().isPresent()) {
            return Optional.of(this.baseTypeForShape(operationShape.getOutput().get()));
        }
        return Optional.empty();
    }

    public String validityPredicateForShape(final ShapeId shapeId) {
        final String unqualifiedTypeName = baseTypeForShape(shapeId);
        return "IsValid_%s".formatted(unqualifiedTypeName);
    }

    /**
     * Returns the Dafny module corresponding to the namespace of the given shape ID.
     */
    public static String dafnyModuleForShapeId(final ShapeId shapeId) {
        final Stream<String> namespaceParts = Arrays
                .stream(shapeId.getNamespace().split("\\."))
                .map(StringUtils::capitalize);
        return Joiner.on('.').join(namespaceParts.iterator());
    }

    /**
     * Returns the Dafny {@code {:extern}} namespace corresponding to the namespace of the given shape ID.
     */
    public static String dafnyExternNamespaceForShapeId(final ShapeId shapeId) {
        return "Dafny." + dafnyModuleForShapeId(shapeId);
    }

    public String predicateSucceededWith(OperationShape operationShape) {
        return "%sSucceededWith".formatted(this.methodForOperation(operationShape));
    }
}
