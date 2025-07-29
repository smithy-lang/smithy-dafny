// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.FROM_DAFNY;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.TO_DAFNY;

import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Function;
import java.util.stream.Collectors;
import java.util.stream.Stream;

import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.utils.DafnyNameResolverHelpers;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.Token;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.*;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.utils.StringUtils;

/**
 * Generates a {@code TypeConversion} class that includes all {@link TypeConversionCodegen.TypeConverter}s needed
 * for AWS SDK-specific types.
 */
public class AwsSdkTypeConversionCodegen extends TypeConversionCodegen {

  private static final ShapeId SMITHY_STRING_SHAPE_ID = ShapeId.from(
    "smithy.api#String"
  );

  public AwsSdkTypeConversionCodegen(
    final Model model,
    final ServiceShape serviceShape
  ) {
    super(
      model,
      serviceShape,
      new AwsSdkDotNetNameResolver(model, serviceShape)
    );
  }

  public Set<ShapeId> findShapeIdsToConvert() {
    Set<ShapeId> shapeIds = super.findShapeIdsToConvert();
    shapeIds.add(SMITHY_STRING_SHAPE_ID); // needed for converting the message of an unknown error type
    return shapeIds;
  }

  /**
   * Returns a set of shape IDs for which to start generating type converter pairs, by recursively traversing
   * services, resources, and operations defined in the model.
   * <p>
   * Since type converters are only necessary when calling API operations, it suffices to find the shape IDs of:
   * <ul>
   *     <li>operation input and output structures</li>
   *     <li>client configuration structures</li>
   *     <li>specific (modeled) error structures</li>
   * </ul>
   */
  protected Set<ShapeId> findInitialShapeIdsToConvert() {
    // Collect services
    final Set<ServiceShape> serviceShapes = model
      .getServiceShapes()
      .stream()
      .filter(serviceShape -> isInServiceNamespace(serviceShape.getId()))
      .collect(Collectors.toSet());

    // Collect resources defined in model...
    final Stream<ResourceShape> topLevelResourceShapes = model
      .getResourceShapes()
      .stream()
      .filter(resourceShape -> isInServiceNamespace(resourceShape.getId()));
    // ... and resources of collected services.
    final Stream<ResourceShape> serviceResourceShapes = serviceShapes
      .stream()
      .flatMap(serviceShape -> serviceShape.getResources().stream())
      .map(resourceShapeId ->
        model.expectShape(resourceShapeId, ResourceShape.class)
      );
    final Set<ResourceShape> resourceShapes = Stream
      .concat(topLevelResourceShapes, serviceResourceShapes)
      .collect(Collectors.toSet());

    // Collect operations defined in model...
    final Stream<OperationShape> topLevelOperationShapes = model
      .getOperationShapes()
      .stream()
      .filter(operationShape -> isInServiceNamespace(operationShape.getId()));
    // ... and operations of collected services...
    final Stream<OperationShape> serviceOperationShapes = serviceShapes
      .stream()
      .flatMap(serviceShape -> serviceShape.getAllOperations().stream())
      .map(operationShapeId ->
        model.expectShape(operationShapeId, OperationShape.class)
      );
    // ... and operations of collected resources.
    final Stream<OperationShape> resourceOperationShapes = resourceShapes
      .stream()
      .flatMap(resourceShape -> resourceShape.getAllOperations().stream())
      .map(operationShapeId ->
        model.expectShape(operationShapeId, OperationShape.class)
      );
    final Set<OperationShape> operationShapes = Stream
      .of(
        topLevelOperationShapes,
        serviceOperationShapes,
        resourceOperationShapes
      )
      .flatMap(Function.identity())
      .collect(Collectors.toSet());
    // Collect inputs/output structures for collected operations
    final Set<ShapeId> operationStructures = operationShapes
      .stream()
      .flatMap(operationShape ->
        Stream
          .of(operationShape.getInput(), operationShape.getOutput())
          .flatMap(Optional::stream)
      )
      .collect(Collectors.toSet());
    // Collect service client config structures
    final Set<ShapeId> clientConfigStructures = serviceShapes
      .stream()
      .map(serviceShape -> serviceShape.getTrait(LocalServiceTrait.class))
      .flatMap(Optional::stream)
      .map(LocalServiceTrait::getConfigId)
      .collect(Collectors.toSet());

    // Collect union shapes
    final Set<ShapeId> unionShapes = model
      .getUnionShapes()
      .stream()
      .filter(unionShape -> isInServiceNamespace(unionShape.getId()))
      .map(unionShape -> unionShape.getId())
      .collect(Collectors.toSet());

    // TODO add smithy v2 Enums
    // Collect enum shapes
    final Set<ShapeId> enumShapes = model
      .getShapesWithTrait(EnumTrait.class)
      .stream()
      .map(Shape::getId)
      .filter(this::isInServiceNamespace)
      .collect(Collectors.toSet());

    // Collect all specific error structures
    final Set<ShapeId> errorStructures = ModelUtils
      .streamServiceErrors(model, serviceShape)
      .map(Shape::getId)
      .collect(Collectors.toSet());

    // Collect into TreeSet so that we generate code in a deterministic order (lexicographic, in particular)
    final TreeSet<ShapeId> orderedSet = new TreeSet<ShapeId>();
    orderedSet.addAll(operationStructures);
    orderedSet.addAll(clientConfigStructures);
    orderedSet.addAll(unionShapes);
    orderedSet.addAll(errorStructures);
    orderedSet.addAll(enumShapes);
    return orderedSet;
  }

  @Override
  public TypeConverter generateStructureConverter(
    final StructureShape structureShape
  ) {
    if (structureShape.hasTrait(ErrorTrait.class)) {
      return generateSpecificModeledErrorConverter(structureShape);
    }

    return super.generateStructureConverter(structureShape);
  }

  /**
   * We can't call the {@code IsSet} methods on AWS SDK classes' member properties because they're internal.
   * The best we can do is to call the properties' getters, which calls {@code GetValueOrDefault}, which in turn may
   * improperly coalesce absent optional values to 0 (for example).
   */
  @Override
  public TokenTree generateExtractOptionalMember(MemberShape memberShape) {
    final String type;
    if (
      StringUtils.equals(
        nameResolver.baseTypeForShape(memberShape.getId()),
        AwsSdkDotNetNameResolver.DDB_ATTRIBUTE_VALUE_MODEL_NAMESPACE
      )
    ) {
      type = AwsSdkDotNetNameResolver.DDB_V2_ATTRIBUTE_VALUE;
    } else {
      type = nameResolver.baseTypeForShape(memberShape.getId());
    }
    final String varName = nameResolver.variableNameForClassProperty(
      memberShape
    );
    final String propertyName = nameResolver.classPropertyForStructureMember(
      memberShape
    );
    return TokenTree.of(type, varName, "= value.%s;".formatted(propertyName));
  }

  @Override
  protected boolean enumListAndMapMembersAreStringsInCSharp() {
    return true;
  }

  public record DafnyConverterBodies(
    TokenTree fromDafnyBody,
    TokenTree toDafnyBody
  ) {}

  DafnyConverterBodies generateAwsSdkServiceReferenceStructureConverter(
    final StructureShape structureShape
  ) {
    final String sdkServiceImpl =
      ((AwsSdkDotNetNameResolver) nameResolver).implForServiceClient();

    final String serviceClientShim =
      "%s.%s".formatted(
          ((AwsSdkDotNetNameResolver) nameResolver).syntheticNamespaceForService(),
          ((AwsSdkDotNetNameResolver) nameResolver).shimClassForService()
        );
    final String serviceInterfaceType = nameResolver.baseTypeForShape(
      serviceShape.getId()
    );

    final String throwCustomImplException =
      "throw new System.ArgumentException(\"Custom implementations of %s are not supported yet\");".formatted(
          serviceInterfaceType
        );
    final TokenTree fromDafnyBody = Token.of(
      "if (value is %s shim) { return shim._impl; }".formatted(
          serviceClientShim
        ),
      throwCustomImplException
    );
    final TokenTree toDafnyBody = TokenTree.of(
      "if (value is %s impl) { return new %s(impl); }".formatted(
          sdkServiceImpl,
          serviceClientShim
        ),
      throwCustomImplException
    );

    return new DafnyConverterBodies(fromDafnyBody, toDafnyBody);
  }

  @Override
  protected String getTypeConversionNamespace() {
    return (
      (AwsSdkDotNetNameResolver) nameResolver
    ).syntheticNamespaceForService();
  }

  /**
   * No unmodeled converters are needed for the AWS SDK shims.
   */
  @Override
  protected Stream<TypeConverter> generateUnmodeledConverters() {
    return Stream.of(generateCommonExceptionConverter());
  }

  @Override
  protected TokenTree errorToDafnyBody(
    final TreeSet<StructureShape> errorShapes
  ) {
    final String dafnyUnknownErrorType =
      "%s.Error_OpaqueWithText".formatted(
          DafnyNameResolverHelpers.dafnyExternNamespaceForShapeId(
            serviceShape.getId()
          )
        );

    // Collect into TreeSet so that we generate code in a deterministic order (lexicographic, in particular)
    final TokenTree knownErrorCases = TokenTree
      .of(
        errorShapes
          .stream()
          .map(errorShape -> {
            final ShapeId errorShapeId = errorShape.getId();
            final String sdkErrorType = nameResolver.baseTypeForShape(
              errorShapeId
            );
            final String errorConverter =
              DotNetNameResolver.qualifiedTypeConverter(errorShapeId, TO_DAFNY);
            // InvalidEndpointException does not exist in v2 of the sdk
            if (sdkErrorType.endsWith("InvalidEndpointException")) {
              return Token.of("");
            }
            return Token.of(
              """
              case %s e:
                  return %s(e);
              """.formatted(sdkErrorType, errorConverter)
            );
          })
      )
      .lineSeparated();

    final TokenTree unknownErrorCase = Token.of(
      """
      default:
          return new %s(value, Dafny.Sequence<char>.FromString(value.ToString()));
      """.formatted(dafnyUnknownErrorType)
    );
    final TokenTree cases = TokenTree
      .of(knownErrorCases, unknownErrorCase)
      .lineSeparated();
    final TokenTree body = Token.of("switch (value)").append(cases.braced());
    return body;
  }

  @Override
  protected TokenTree errorFromDanyBody(
    final TreeSet<StructureShape> errorShapes
  ) {
    // Handle the modeled exceptions.
    final TokenTree modeledExceptionsFromDafny = TokenTree
      .of(
        errorShapes
          .stream()
          .map(errorShape -> {
            final ShapeId modeledErrorShapeId = errorShape.getId();
            if (
              modeledErrorShapeId.getName().endsWith("InvalidEndpointException")
            ) {
              return Token.of("");
            }
            return Token.of(
              "case %1$s dafnyVal:\nreturn %2$s(dafnyVal);".formatted(
                  nameResolver.dafnyTypeForShape(modeledErrorShapeId),
                  DotNetNameResolver.typeConverterForShape(
                    modeledErrorShapeId,
                    FROM_DAFNY
                  )
                )
            );
          })
      )
      .lineSeparated();

    // Handle the special cases that were cast to the root service exception.
    // TODO: We could look up the AWS SDK Base Service Exception, and possibly return that...
    final TokenTree handleBaseFromDafny = TokenTree
      .of(
        "case %1$s dafnyVal:".formatted(
            DotNetNameResolver.dafnyUnknownWithTextErrorTypeForServiceShape(
              serviceShape
            )
          ),
        "return new SystemException(dafnyVal._obj.ToString());",
        "default:",
        "// The switch MUST be complete for _IError, so `value` MUST NOT be an _IError. (How did you get here?)",
        "return new SystemException();;"
      )
      .lineSeparated();

    // Wrap all the converters into a switch statement.
    final TokenTree fromDafnySwitchCases = TokenTree
      .of(modeledExceptionsFromDafny, handleBaseFromDafny)
      .lineSeparated()
      .braced();

    final TokenTree fromDafnyBody = TokenTree
      .of(TokenTree.of("switch(value)"), fromDafnySwitchCases)
      .lineSeparated();
    return fromDafnyBody;
  }
}
