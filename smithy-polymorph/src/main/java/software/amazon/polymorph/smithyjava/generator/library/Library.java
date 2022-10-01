package software.amazon.polymorph.smithyjava.generator.library;

import java.nio.file.Path;
import java.util.HashMap;
import java.util.Map;

import software.amazon.polymorph.smithyjava.NamespaceHelper;
import software.amazon.polymorph.smithyjava.generator.CodegenSubject;
import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.smithyjava.nameresolver.Native;
import software.amazon.polymorph.utils.DafnyNameResolverHelpers;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;

public class Library extends CodegenSubject {

    /** Public Java Interfaces will go here. */
    public final String packageName;
    /** Public POJOs will go here. */
    public final String modelPackageName;

    public Library(Model model, ServiceShape serviceShape) {
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
        Map<Path, TokenTree> rtn = new HashMap<>();
        ModelCodegen serviceCodegen = new ModelCodegen(this);
        rtn.putAll(serviceCodegen.generate());
        return rtn;
    }
}
