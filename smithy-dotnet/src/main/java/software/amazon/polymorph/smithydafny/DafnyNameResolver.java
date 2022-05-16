// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydafny;

import com.google.common.base.Joiner;

import software.amazon.polymorph.traits.PositionalTrait;
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

import java.nio.file.Path;
import javax.annotation.Nullable;
import java.util.Arrays;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.stream.Stream;
import java.util.HashSet;

public record DafnyNameResolver(
  Model model,
  ServiceShape serviceShape,
  HashSet<DependentSmithyModel> dependentModels,
  Path[] dependentModelPaths
) {

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

    public static String nameForService(final ServiceShape serviceShape) {
        return StringUtils.capitalize(serviceShape.getId().getName());
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
                    LIST, MAP -> dafnyModulePrefixForShapeId(shape) + shapeName;
            case STRUCTURE -> {
                if (shape.hasTrait(ReferenceTrait.class)) {
                    yield baseTypeForShape(shape.expectTrait(ReferenceTrait.class).getReferentId());
                } else if (shape.hasTrait(PositionalTrait.class)) {
                    final StructureShape structure = shape.asStructureShape().get();
                    if (structure.getMemberNames().size() != 1) {
                        throw new IllegalStateException("Positional trait only supports a single member.");
                    }
                    final MemberShape member = structure
                      .getMember(structure.getMemberNames().get(0))
                      .get();
                    yield baseTypeForShape(member.getTarget());
                } else {
                    yield dafnyModulePrefixForShapeId(shape) + shapeName;
                }
            }
            case SERVICE -> traitForServiceClient(shape.asServiceShape().get());
            case RESOURCE -> traitForResource(shape.asResourceShape().get());
            // Member calls baseTypeForShape...
            case MEMBER -> baseTypeForMember(shape.asMemberShape().get());
            // TODO create/use better timestamp type in Dafny libraries
            case TIMESTAMP -> "string";
            default -> throw new UnsupportedOperationException(
                    "Shape %s has unsupported type %s".formatted(shapeId, shape.getType()));
        };
    }

    private String baseTypeForMember(final MemberShape memberShape) {
        final String targetType = baseTypeForShape(memberShape.getTarget());

        if (!ModelUtils.memberShapeIsOptional(model, memberShape)) {
            return targetType;
        }

        return ("Option<%s>").formatted(targetType);
    }

    public String generatedTypeForShape(final ShapeId shapeId) {
        return StringUtils.capitalize(shapeId.getName(serviceShape));
    }

    public String traitForServiceClient(final ServiceShape serviceShape) {
        return dafnyModulePrefixForShapeId(serviceShape) + "I%sClient".formatted(nameForService(serviceShape));
    }

    public String traitForResource(final ResourceShape resourceShape) {
        final ShapeId shapeId = resourceShape.getId();
        final String resourceName = StringUtils.capitalize(shapeId.getName(this.serviceShape));
        return dafnyModulePrefixForShapeId(resourceShape) + "I%s".formatted(resourceName);
    }

    public String traitForServiceError(final ServiceShape serviceShape) {
        return "I%sException".formatted(nameForService(serviceShape));
    }

    public String classForSpecificError(final StructureShape structureShape) {
        return StringUtils.capitalize(structureShape.getId().getName());
    }

    public static String classForUnknownError(final ServiceShape serviceShape) {
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

    public static String dafnyModuleForNamespace(final String namespace) {
        final Stream<String> namespaceParts = Arrays
          .stream(namespace.split("\\."))
          .map(StringUtils::capitalize);
        return Joiner.on('.').join(namespaceParts.iterator());
    }

    public static String dafnyModuleForShapeId(final ShapeId shapeId) {
        return  dafnyModuleForNamespace(shapeId.getNamespace());
    }

    public static String dafnyAbstractModuleForNamespace(final String namespace) {
        return dafnyModuleForNamespace(namespace) + "Abstract";
    }

    public String localDafnyModuleName(final String namespace) {
        // Don't want to `open` everything,
        // so I need the module name prefix
        final String[] tmp = dafnyModuleForNamespace(namespace).split("\\.");
        return tmp[tmp.length - 1 ];
    }

    public String dafnyModulePrefixForShapeId(final Shape shape) {
        final String namespace = shape.getId().getNamespace();
        if (!serviceShape.toShapeId().getNamespace().equals(namespace)) {

            // Unfortunate side effect
            // Need to add these so that they can be included
            // because we are obviously using them!
            dependentModels
              .add(DependentSmithyModel.of(shape, dependentModelPaths));

            // Append `.` so that it is easy to use.
            // If you only want the name use localDafnyModuleName
            return localDafnyModuleName(namespace) + ".";
        } else {
            // This is "local" and so does not need any Module name...
            return "";
        }
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
