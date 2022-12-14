// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet;

import java.util.Set;
import java.util.stream.Stream;

import software.amazon.polymorph.utils.Token;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.*;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.utils.StringUtils;

/**
 * Generates a {@code TypeConversion} class that includes all {@link TypeConversionCodegen.TypeConverter}s needed
 * for AWS SDK-specific types.
 */
public class AwsSdkTypeConversionCodegen extends TypeConversionCodegen {
    private static final ShapeId SMITHY_STRING_SHAPE_ID = ShapeId.from("smithy.api#String");

    public AwsSdkTypeConversionCodegen(final Model model, final ServiceShape serviceShape) {
        super(model, serviceShape,
                new AwsSdkDotNetNameResolver(model, serviceShape));
    }

    @Override
    public Set<ShapeId> findShapeIdsToConvert() {
        final Set<ShapeId> shapeIds = super.findShapeIdsToConvert();
        shapeIds.add(SMITHY_STRING_SHAPE_ID);  // needed for converting the message of an unknown error type
        return shapeIds;
    }

    @Override
    public TypeConverter generateStructureConverter(final StructureShape structureShape) {
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
        final String type = StringUtils.equals(nameResolver.baseTypeForShape(memberShape.getId()), AwsSdkDotNetNameResolver.DDB_ATTRIBUTE_VALUE_MODEL_NAMESPACE)
                ? AwsSdkDotNetNameResolver.DDB_V2_ATTRIBUTE_VALUE
                : nameResolver.baseTypeForShape(memberShape.getId());
        final String varName = nameResolver.variableNameForClassProperty(memberShape);
        final String propertyName = nameResolver.classPropertyForStructureMember(memberShape);
        // In DynamoDB there are three edge cases for the Structures of ConsumedCapacityUnits and for SizeEstimateRangeGB
        // The underlying data type is double but the conversion needs to be type int we will have to manually update these variables
        // and for SizeEstimateRangeGB we have to convert the list of doubles to list of ints
        if (StringUtils.equals(memberShape.getTarget().getName(), "ConsumedCapacityUnits")) {
            return TokenTree.of(
                    type,
                    varName,
                    "= (int) value.%s;".formatted(propertyName));
        } else if (StringUtils.equals(propertyName, "SizeEstimateRangeGB")) {
            // Polymorph type casts the value; however when it is a list you cannot just typecast a list of type x to type y
            // you need to convert the list. In this case we know it is converting the type of the list to int
            return TokenTree.of(
                    type,
                    varName,
                    "= value.%s.Select(i => (int) i).ToList();".formatted(propertyName));
        } else {
            return TokenTree.of(
                    type,
                    varName,
                    "= value.%s;".formatted(propertyName));
        }
    }

    @Override
    protected boolean enumListMembersAreStringsInCSharp() {
        return true;
    }

    TypeConverter generateAwsSdkServiceReferenceStructureConverter(final StructureShape structureShape) {
        final String sdkServiceImpl = ((AwsSdkDotNetNameResolver) nameResolver).implForServiceClient();


        final String serviceClientShim = "%s.%s".formatted(
                ((AwsSdkDotNetNameResolver) nameResolver).syntheticNamespaceForService(),
                ((AwsSdkDotNetNameResolver) nameResolver).shimClassForService());
        final String serviceInterfaceType = nameResolver.baseTypeForShape(serviceShape.getId());

        final String throwCustomImplException =
                "throw new System.ArgumentException(\"Custom implementations of %s are not supported yet\");"
                        .formatted(serviceInterfaceType);
        final TokenTree fromDafnyBody = Token.of(
                "if (value is %s shim) { return shim._impl; }".formatted(serviceClientShim),
                throwCustomImplException);
        final TokenTree toDafnyBody = TokenTree.of(
                "if (value is %s impl) { return new %s(impl); }".formatted(sdkServiceImpl, serviceClientShim),
                throwCustomImplException);

        return buildConverterFromMethodBodies(structureShape, fromDafnyBody, toDafnyBody);
    }

    @Override
    protected String getTypeConversionNamespace() {
        return ((AwsSdkDotNetNameResolver)nameResolver).syntheticNamespaceForService();
    }

    /**
     * No unmodeled converters are needed for the AWS SDK shims.
     */
    @Override
    protected Stream<TypeConverter> generateUnmodeledConverters() {
        return Stream.empty();
    }
}
