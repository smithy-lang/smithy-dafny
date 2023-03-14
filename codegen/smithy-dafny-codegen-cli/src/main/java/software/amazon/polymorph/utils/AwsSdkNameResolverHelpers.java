package software.amazon.polymorph.utils;

import software.amazon.smithy.aws.traits.ServiceTrait;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.utils.StringUtils;

/**
 * Static Methods for generating/naming AWS SDK shapes
 */
public class AwsSdkNameResolverHelpers {
    public static String namespaceForService(final String awsServiceName) {
        return "com.amazonaws.%s".formatted(awsServiceName);
    }

    public static String getSdkId(final ServiceShape serviceShape) {
        return serviceShape.getTrait(ServiceTrait.class)
                           .map(t -> t.getSdkId())
                           .orElse(StringUtils.capitalize(awsServiceNameFromShape(serviceShape)));
    }

    // TODO Accept a Shape and check if it is in the closure
    // of a service with the @aws.api#service trait instead
    public static boolean isInAwsSdkNamespace(ShapeId shapeId) {
        return shapeId.getNamespace().startsWith("com.amazonaws.");
    }

    public static String awsServiceNameFromShape(final Shape shape) {
        String[] namespaceParts = shape.getId().getNamespace().split("\\.");
        return namespaceParts[namespaceParts.length - 1];
    }

    public static ServiceShape getAwsServiceShape(final Model model, final ShapeId shapeId) {
        if (!isInAwsSdkNamespace(shapeId)) throw new IllegalStateException("Shape is not in an AWS SKD namespace:" + shapeId.getName() + ", " + shapeId.getNamespace());

        return ModelUtils.serviceFromNamespace(model, shapeId.getNamespace());
    }
}
