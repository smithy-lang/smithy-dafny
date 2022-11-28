package software.amazon.polymorph.smithyjava.generator.library;

import java.nio.file.Path;
import java.util.HashMap;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import software.amazon.polymorph.smithyjava.NamespaceHelper;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.smithyjava.nameresolver.Native;
import software.amazon.polymorph.utils.DafnyNameResolverHelpers;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;
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

    public JavaLibrary(Model model, ServiceShape serviceShape) {
        super(model, serviceShape, initDafny(model, serviceShape), initNative(model, serviceShape));
        packageName = NamespaceHelper.standardize(serviceShape.getId().getNamespace());
        modelPackageName = packageName + ".model";
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
}
