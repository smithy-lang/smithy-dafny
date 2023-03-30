package software.amazon.polymorph.smithyjava.generator.library;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.CodeBlock;
import com.squareup.javapoet.MethodSpec;

import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import software.amazon.polymorph.smithyjava.NamespaceHelper;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.polymorph.smithyjava.generator.Generator;
import software.amazon.polymorph.smithyjava.generator.awssdk.v1.ShimV1;
import software.amazon.polymorph.smithyjava.generator.awssdk.v2.ShimV2;
import software.amazon.polymorph.smithyjava.generator.library.shims.ResourceShim;
import software.amazon.polymorph.smithyjava.generator.library.shims.ServiceShim;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.polymorph.utils.DafnyNameResolverHelpers;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.smithyjava.nameresolver.Native;

import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.node.ExpectationNotMetException;
import software.amazon.smithy.model.shapes.ListShape;
import software.amazon.smithy.model.shapes.MapShape;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ResourceShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.SetShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.TraitDefinition;

public class JavaLibrary extends CodegenSubject {

    /** Public Java Interfaces will go here. */
    public final String packageName;
    /** Public POJOs will go here. */
    public final String modelPackageName;
    protected final ToDafnyLibrary toDafnyLibrary;
    protected final ToNativeLibrary toNativeLibrary;

    public JavaLibrary(Model model, ServiceShape serviceShape, AwsSdkVersion sdkVersion) {
        super(model, serviceShape, initDafny(model, serviceShape, sdkVersion), initNative(model, serviceShape, sdkVersion), sdkVersion);
        packageName = NamespaceHelper.standardize(serviceShape.getId().getNamespace());
        modelPackageName = packageName + ".model";
        try {
            serviceShape.expectTrait(LocalServiceTrait.class);
        } catch (ExpectationNotMetException ex) {
            throw new IllegalArgumentException(
                    "JavaLibrary's MUST have a localService trait. ShapeId: %s".formatted(serviceShape.getId()),
                    ex
            );
        }
        toDafnyLibrary = new ToDafnyLibrary(this);
        toNativeLibrary = new ToNativeLibrary(this);
    }

    static Dafny initDafny(Model model, ServiceShape serviceShape, AwsSdkVersion awsSdkVersion) {
        String packageName = DafnyNameResolverHelpers.packageNameForNamespace(serviceShape.getId().getNamespace());
        return new Dafny(packageName, model, serviceShape, awsSdkVersion);
    }

    static Native initNative(Model model, ServiceShape serviceShape, AwsSdkVersion awsSdkVersion) {
        String packageName = NamespaceHelper.standardize(serviceShape.getId().getNamespace());
        return new Native(packageName, serviceShape, model, packageName + ".model", awsSdkVersion);
    }

    public static CodeBlock wrapAwsService(
            Shape shape, CodeBlock nativeValue, CodeBlock regionVar,
            AwsSdkVersion sdkVersion) {
        Optional<ServiceShape> serviceShape = shape.asServiceShape();
        if (serviceShape.isEmpty()) {
            throw new IllegalArgumentException("Shape must be Service");
        }
        return switch (sdkVersion) {
            case V1 -> CodeBlock.of("new $T($L, $L)",
                    ShimV1.className(serviceShape.get()),
                    nativeValue,
                    regionVar);
            case V2 -> CodeBlock.of("new $T($L, $L)",
                    ShimV2.className(serviceShape.get()),
                    nativeValue,
                    regionVar);
        };
    }

    @SuppressWarnings("unused") // We do not use this yet (2023-03-05), but we might soon-ish. Remove by 2023-06 if still not used.
    protected static CodeBlock castAndUnwrapAwsService(
            Shape shape, CodeBlock dafnyValue,
            AwsSdkVersion sdkVersion) {
        Optional<ServiceShape> serviceShape = shape.asServiceShape();
        if (serviceShape.isEmpty()) {
            throw new IllegalArgumentException("Shape must be Service");
        }
        return switch (sdkVersion) {
            case V1 -> CodeBlock.of("(($T) $L).impl()",
                    ShimV1.className(serviceShape.get()),
                    dafnyValue);
            case V2 -> CodeBlock.of("(($T) $L).impl()",
                    ShimV2.className(serviceShape.get()),
                    dafnyValue);
        };
    }

    /**
     * @param method      MethodSpec.Builder that SHOULD have Parameters,
     *                    Returns, and Modifiers set correctly
     *                    ( note that
     *                    void or parameterless methods would
     *                    not have any Returns or Parameters).
     * @param resolvedInput  A ResolvedShapeId representing the input
     * @param resolvedOutput A ResolvedShapeId representing the output
     */
    public record MethodSignature(
            MethodSpec.Builder method,
            ModelUtils.ResolvedShapeId resolvedInput,
            ModelUtils.ResolvedShapeId resolvedOutput
    ) {}

    @Override
    public Map<Path, TokenTree> generate() {
        Map<Path, TokenTree> rtn = new LinkedHashMap<>();
        ModelCodegen serviceCodegen = new ModelCodegen(this);
        rtn.putAll(serviceCodegen.generate());
        rtn.putAll(toDafnyLibrary.generate());
        rtn.putAll(toNativeLibrary.generate());
        ShimLibrary shim = new ServiceShim(this, this.serviceShape);
        rtn.putAll(shim.generate());
        getResourcesInServiceNamespace().stream()
                .map(shape -> new ResourceShim(this, shape))
                .map(Generator::generate)
                .forEachOrdered(rtn::putAll);
        return rtn;
    }

    public List<StructureShape> getErrorsInServiceNamespace() {
        return this.model.getStructureShapes().stream()
                .filter(shape -> shape.hasTrait(ErrorTrait.class))
                .filter(shape -> ModelUtils.isInServiceNamespace(shape.getId(), this.serviceShape))
                .toList();
    }

    public List<StructureShape> getStructuresInServiceNamespace() {
        return this.model.getStructureShapes().stream()
                .filter(shape -> !shape.hasTrait(ErrorTrait.class))
                .filter(shape -> !shape.hasTrait(TraitDefinition.class))
                .filter(shape -> !shape.hasTrait(EnumTrait.class))
                // We do not generate POJOs or To(Dafny,Native) for reference shapes
                .filter(shape -> !shape.hasTrait(ReferenceTrait.class))
                // We do not generate POJOs or To(Dafny,Native) for indirect reference shapes
                .filter(shape -> {
                    if (!shape.hasTrait(PositionalTrait.class)) {
                        return true;
                    }
                    final MemberShape onlyMember = PositionalTrait.onlyMember(shape);
                    final Shape targetShape = model.expectShape(onlyMember.getTarget());
                    return !targetShape.hasTrait(ReferenceTrait.class);
                })
                .filter(shape -> ModelUtils.isInServiceNamespace(shape.getId(), this.serviceShape))
                .toList();
    }

    public List<ResourceShape> getResourcesInServiceNamespace() {
        return this.model.getResourceShapes().stream()
                .filter(shape -> ModelUtils.isInServiceNamespace(shape.getId(), this.serviceShape))
                .toList();
    }

    public List<StringShape> getEnumsInServiceNamespace() {
        return this.model.getStringShapesWithTrait(EnumTrait.class).stream()
                .filter(shape -> ModelUtils.isInServiceNamespace(shape.getId(), this.serviceShape))
                .toList();
    }

    public List<UnionShape> getUnionsInServiceNamespace() {
        return this.model.getUnionShapes().stream().sequential()
                .filter(shape -> ModelUtils.isInServiceNamespace(shape.getId(), this.serviceShape))
                .collect(Collectors.toList());
    }

    public List<ListShape> getListsInServiceNamespace() {
        return this.model.getListShapes().stream().sequential()
                .filter(shape -> ModelUtils.isInServiceNamespace(shape.getId(), this.serviceShape))
                .collect(Collectors.toList());
    }

    public List<SetShape> getSetsInServiceNamespace() {
        return this.model.getSetShapes().stream().sequential()
                .filter(shape -> ModelUtils.isInServiceNamespace(shape.getId(), this.serviceShape))
                .collect(Collectors.toList());
    }

    public List<MapShape> getMapsInServiceNamespace() {
        return this.model.getMapShapes().stream().sequential()
                .filter(shape -> ModelUtils.isInServiceNamespace(shape.getId(), this.serviceShape))
                .collect(Collectors.toList());
    }

    public CodeBlock wrapWithShim(ShapeId referentId, CodeBlock referentVariable) throws ExpectationNotMetException {
        final Shape targetShape = model.expectShape(referentId);
        final ClassName rtnClassName;
        if (targetShape.isResourceShape()) {
            //noinspection OptionalGetWithoutIsPresent
            ResourceShape rShape = targetShape.asResourceShape().get();
            rtnClassName = nativeNameResolver.classNameForResource(rShape);
            return CodeBlock.of("$T.$L($L)",
                    rtnClassName, ResourceShim.WRAP_METHOD_NAME, referentVariable);
        } else {
            // It MUST be a service, as reference traits ONLY reference Resources & Services
            //noinspection OptionalGetWithoutIsPresent
            ServiceShape sShape = targetShape.asServiceShape().get();
            rtnClassName = nativeNameResolver.classNameForService(sShape);
        }
        return CodeBlock.of("new $T($L)",
                rtnClassName,
                referentVariable);
    }
}
