package software.amazon.polymorph.utils;

import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;

/**
 * Static Methods for generating/naming AWS SDK shapes
 */
public class AwsSdkNameResolverHelpers {
    public static String namespaceForService(final String awsServiceName) {
        return "com.amazonaws.%s".formatted(awsServiceName);
    }

    // TODO better way to determine if AWS SDK
    public static boolean isAwsSdkServiceId(ShapeId serviceShapeId) {
        return serviceShapeId.getNamespace().startsWith("com.amazonaws.");
    }

    public static String awsServiceNameFromShape(final Shape shape) {
        String[] namespaceParts = shape.getId().getNamespace().split("\\.");
        return namespaceParts[namespaceParts.length - 1];
    }
}
