package software.amazon.polymorph.utils;

import com.google.common.base.Joiner;

import java.util.Arrays;
import java.util.stream.Stream;

import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.utils.StringUtils;

/**
 * Static Methods for generating/referring to Dafny modules
 */
public class DafnyNameResolverHelpers {

    /**
     * Returns the Dafny module corresponding to the namespace of the given shape ID.
     */
    public static String dafnyModuleForNamespace(final String namespace) {
        final Stream<String> namespaceParts = Arrays
          .stream(namespace.split("\\."))
          .map(StringUtils::capitalize);
        return Joiner.on('.').join(namespaceParts.iterator()) + ".Types";
    }

    /**
     * Returns the Dafny {@code {:extern}} namespace corresponding to the namespace of the given shape ID.
     */
    public static String dafnyExternNamespaceForShapeId(final ShapeId shapeId) {
        return "Dafny." + dafnyModuleForNamespace(shapeId.getNamespace());
    }
}
