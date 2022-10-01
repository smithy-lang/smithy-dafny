package software.amazon.polymorph.smithyjava.generator;

import java.nio.file.Path;
import java.util.Map;

import software.amazon.polymorph.smithyjava.nameresolver.Dafny;
import software.amazon.polymorph.smithyjava.nameresolver.Native;
import software.amazon.polymorph.utils.TokenTree;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;

/**
 * The Subject of code generation.
 * Provides generators access to Name Resolvers, Model, and Service Shape
 * specific to the subject.
 * Extensions should customize name resolvers.
 */
public abstract class CodegenSubject {

    final public Dafny dafnyNameResolver;
    final public Native nativeNameResolver;
    final public Model model;
    final public ServiceShape serviceShape;

    protected CodegenSubject(
            Model model,
            ServiceShape serviceShape,
            Dafny dafnyNameResolver,
            Native nativeNameResolver
    ) {
        this.model = model;
        this.serviceShape = serviceShape;
        this.dafnyNameResolver = dafnyNameResolver;
        this.nativeNameResolver = nativeNameResolver;
    }


    /**
     * Generates Java Code for the Subject.
     */
    public abstract Map<Path, TokenTree> generate();
}
