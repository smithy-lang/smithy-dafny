package software.amazon.polymorph.utils;

import software.amazon.polymorph.smithydafny.DafnyNameResolver;
import software.amazon.smithy.model.shapes.ShapeId;

/**
 * Static Methods for generating/referring to Dafny modules
 */
public class DafnyNameResolverHelpers {

    /**
     * Returns the Dafny {@code {:extern}} namespace corresponding to the given shape ID,
     * assuming it was generated into a "Types" module.
     */
    public static String dafnyExternNamespaceForShapeId(final ShapeId shapeId) {
        return DafnyNameResolver.dafnyExternNamespaceForNamespace(shapeId.getNamespace()) + ".types";
    }

    /**
     * Returns the Dafny {@code {:extern}} namespace corresponding to the namespace,
     * but NOT the Types module.
     */
    public static String packageNameForNamespace(final String namespace) {
        return DafnyNameResolver.dafnyExternNamespaceForNamespace(namespace);
    }

    /** @return The __default for a namespace.*/
    public static String defaultForNamespace(final String namespace){
        return packageNameForNamespace(namespace) + ".__default";
    }

    public static String dafnyCompilesExtra_(final String name) {
        return name.replace("_", "__");
    }
}
