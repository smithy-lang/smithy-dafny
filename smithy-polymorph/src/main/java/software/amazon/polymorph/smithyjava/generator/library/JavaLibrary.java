package software.amazon.polymorph.smithyjava.generator.library;

import java.nio.file.Path;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.stream.Collectors;

import software.amazon.polymorph.smithyjava.NamespaceHelper;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.smithyjava.nameresolver.Native;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.PositionalTrait;
import software.amazon.polymorph.utils.DafnyNameResolverHelpers;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.node.ExpectationNotMetException;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.OperationShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StringShape;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.TraitDefinition;

public class JavaLibrary extends CodegenSubject {

    /** Public Java Interfaces will go here. */
    public final String packageName;
    /** Public POJOs will go here. */
    public final String modelPackageName;
    /** Public Interface/Class consumers interact with.*/
    protected final String publicClass;
    /** Config object required to create the public interface.*/
    protected final ShapeId publicConfigShapeId;

    public JavaLibrary(Model model, ServiceShape serviceShape) {
        super(model, serviceShape, initDafny(model, serviceShape), initNative(model, serviceShape));
        packageName = NamespaceHelper.standardize(serviceShape.getId().getNamespace());
        modelPackageName = packageName + ".model";
        try {
            LocalServiceTrait trait = serviceShape.expectTrait(LocalServiceTrait.class);
            this.publicClass = trait.getSdkId();
            this.publicConfigShapeId = trait.getConfigId();
        } catch (ExpectationNotMetException ex) {
            throw new IllegalArgumentException(
                    "JavaLibrary's MUST have a localService trait. ShapeId: %s".formatted(serviceShape.getId()),
                    ex
            );
        }
    }

    static Dafny initDafny(Model model, ServiceShape serviceShape) {
        String packageName = DafnyNameResolverHelpers.packageNameForNamespace(serviceShape.getId().getNamespace());
        return new Dafny(packageName, model, serviceShape);
    }

    static Native initNative(Model model, ServiceShape serviceShape) {
        String packageName = NamespaceHelper.standardize(serviceShape.getId().getNamespace());
        return new Native(packageName, serviceShape, model, packageName + ".model");
    }

    @Override
    public Map<Path, TokenTree> generate() {
        Map<Path, TokenTree> rtn = new LinkedHashMap<>();
        ModelCodegen serviceCodegen = new ModelCodegen(this);
        rtn.putAll(serviceCodegen.generate());
        ToDafnyLibrary toDafny = new ToDafnyLibrary(this);
        rtn.putAll(toDafny.generate());
        ToNativeLibrary toNative = new ToNativeLibrary(this);
        rtn.putAll(toNative.generate());
        ShimLibrary shim = new ShimLibrary(this);
        rtn.putAll(shim.generate());
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
                .filter(shape -> ModelUtils.isInServiceNamespace(shape.getId(), this.serviceShape))
                .toList();
    }

    public List<StringShape> getEnumsInServiceNamespace() {
        return this.model.getStringShapesWithTrait(EnumTrait.class).stream()
                .filter(shape -> ModelUtils.isInServiceNamespace(shape.getId(), this.serviceShape))
                .toList();
    }

    public List<OperationShape> getOperationsInServiceNamespace() {
        return this.model.getOperationShapes().stream().sequential()
                .filter(shape -> ModelUtils.isInServiceNamespace(shape.getId(), this.serviceShape))
                .collect(Collectors.toList());
    }

    protected ShapeId checkForPositional(ShapeId originalId) {
        Shape originalShape = model.expectShape(originalId);
        if (originalShape.hasTrait(PositionalTrait.class)) {
            // Positional traits can only be on structures,
            // asStructureShape cannot return an empty optional
            //noinspection OptionalGetWithoutIsPresent
            MemberShape onlyMember = PositionalTrait.onlyMember(originalShape.asStructureShape().get());
            return onlyMember.getTarget();
        }
        return originalId;
    }
}
