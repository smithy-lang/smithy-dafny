// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithydotnet.localServiceWrapper;

import software.amazon.polymorph.smithydotnet.TypeConversionCodegen;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.*;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import static software.amazon.polymorph.smithydotnet.DotNetNameResolver.typeConverterForShape;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.FROM_DAFNY;
import static software.amazon.polymorph.smithydotnet.TypeConversionDirection.TO_DAFNY;

/**
 * Generates a {@code TypeConversion} class that includes all {@link TypeConverter}s needed
 * for LocalService-specific types.
 * The purpose here is to wrap an existing LocalService
 * mostly for testing.
 */
public class LocalServiceWrappedConversionCodegen extends TypeConversionCodegen {
    private static final Logger LOGGER = LoggerFactory.getLogger(LocalServiceWrappedConversionCodegen.class);

    public LocalServiceWrappedConversionCodegen(final Model model, final ServiceShape serviceShape) {
        super(model, serviceShape,
                new LocalServiceWrappedNameResolver(model, serviceShape));
    }


    // TODO override generateCommonExceptionConverter
    // At this time we generate the same code
    // but really we should defer `ToDafny_CommonError`
    // to the wrapped type converter.

    @Override
    protected TypeConverter buildConverterFromMethodBodies(
      final Shape shape,
      final TokenTree fromDafnyBody,
      final TokenTree toDafnyBody
    ) {

        // In this case we want to ONLY wrap resources
        // in the Wrapped namespace.
        final boolean shouldWrapLocalResource = shouldWrapLocalResource(shape);

        if (!shouldWrapLocalResource) {
            return super.buildConverterFromMethodBodies(shape, fromDafnyBody, toDafnyBody);
        } else {
            // This is going to create nested resources!
            // This means every time a resource crosses into Dafny
            // it will be wrapped again.
            // This is NOT for PRODUCTION
            // This is for test vectors and general correctness testing!
            // On the upside,
            // when such resources are tested,
            // This wrapped NativeWrapper will be exercised
            // as well as the normal .NET wrapper.
            // While this _does not_ test the NativeWrapper
            // in the wrapped module,
            // These two classes are generated by the same code.
            // So there is some analog.
            // See the type conversions for Resources
            // for more details.

            final ShapeId id = shape.getId();
            if (id.getNamespace().equals("simple.resources") && (
                    id.getName().equals("SimpleResource") || id.getName().equals("SimpleResourceReference")
            )) {
                LOGGER.info("Trying to Use a NativeWrapper for SimpleResource Conversion.");
                LOGGER.info("Hard coded catch is executing; preventing SimpleResources' Resource from using a wrapper.");
                return super.buildConverterFromMethodBodies(shape, fromDafnyBody, toDafnyBody);
            }
            final ShapeId resourceShapeId = shape.expectTrait(ReferenceTrait.class).getReferentId();
            final String dafnyType = nameResolver.dafnyTypeForShape(id);
            final String cSharpType = nameResolver.baseTypeForShape(id);

            final String fromDafnyConverterName = typeConverterForShape(shape.getId(), FROM_DAFNY);
            final TokenTree fromDafnyConverterSignature = TokenTree.of(
              "internal static", cSharpType, fromDafnyConverterName, "(%s value)".formatted(dafnyType));

            final String toDafnyConverterName = typeConverterForShape(shape.getId(), TO_DAFNY);
            final TokenTree toDafnyConverterSignature = TokenTree.of(
              "internal static", dafnyType, toDafnyConverterName, "(%s value)".formatted(cSharpType));

            final String namespaceForReferent = nameResolver.namespaceForShapeId(id);
            final TokenTree fromDafnyBodyOverride = TokenTree
              .of(
                "// This is converting a reference type in a dependant module.",
                "// Therefore it defers to the dependant module for conversion",
                "return %s.TypeConversion.%s(value);"
                  .formatted(
                    namespaceForReferent,
                    fromDafnyConverterName
                  )

              )
              .lineSeparated();

            final TokenTree toDafnyBodyOverride = TokenTree
              .of(
                "// This is converting a reference type in a dependant module.",
                "// Therefore it defers to the dependant module for conversion",
                "return new %s((%s)value);"
                  .formatted(
                    nameResolver.nativeWrapperClassForResource(resourceShapeId),
                    nameResolver.baseClassForResource(resourceShapeId)
                  )
              )
              .lineSeparated();

            final TokenTree fromDafnyConverterMethod = TokenTree.of(fromDafnyConverterSignature, fromDafnyBodyOverride.braced());
            final TokenTree toDafnyConverterMethod = TokenTree.of(toDafnyConverterSignature, toDafnyBodyOverride.braced());
            return new TypeConverter(shape.getId(), fromDafnyConverterMethod, toDafnyConverterMethod);
        }
    }

    /**
     * To test @extendable resources they need to be wrapped
     * This wrap/unwrap happens in TypeConversion.
     * However, the conversions are build to avoid nesting
     * and to be generally correct.
     * This means if we want to test the type conversion
     * for operations on a resource we need some additional wrapping.
     * Because the NativeWrappers are not public
     * we build our own NativeWrappers and then wrap any such resource.
     *
     * But here is the rub.
     * We need to identify resources that are
     *  - @extendable
     *  - In the module we are wrapping
     *
     *  Resources that are not @extendable can not be wrapped at this time.
     *  Resources in dependent modules are not under test.
     *
     *
     */
    private Boolean shouldWrapLocalResource(final Shape shape)
    {
        if (ModelUtils.isReferenceDependantModuleType(shape, nameResolver.namespaceForService())) {
            final ShapeId resourceShapeId = shape.expectTrait(ReferenceTrait.class).getReferentId();
            return nameResolver.namespaceForShapeId(serviceShape.getId())
              .equalsIgnoreCase(resourceShapeId.getNamespace());
        } else {
            return false;
        }
    }
}
