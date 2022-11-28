package software.amazon.polymorph.utils;

import software.amazon.polymorph.smithydafny.DafnyNameResolver;
import software.amazon.smithy.model.shapes.ShapeId;

/**
 * Static Methods for generating/referring to Dafny modules
 */
public class DafnyNameResolverHelpers {

    /**
     * Returns the Dafny {@code {:extern}} namespace corresponding to the namespace of the given shape ID.
     */
    public static String dafnyExternNamespaceForShapeId(final ShapeId shapeId) {
        return "Dafny." + DafnyNameResolver.dafnyModuleForNamespace(shapeId.getNamespace());
    }

    /**
     * Returns the Dafny {@code {:extern}} namespace corresponding to the namespace,
     * but NOT the Types module.
     */
    public static String packageNameForNamespace(final String namespace) {
        return "Dafny." + DafnyNameResolver.dafnyNamespace(namespace);
    }

    public static String dafnyCompilesExtra_(final String name) {
        return name.replace("_", "__");
    }
}
