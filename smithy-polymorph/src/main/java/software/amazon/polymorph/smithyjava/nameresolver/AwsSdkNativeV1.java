package software.amazon.polymorph.smithyjava.nameresolver;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.TypeName;

import java.util.Map;

import software.amazon.polymorph.utils.AwsSdkNameResolverHelpers;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.TraitDefinition;
import software.amazon.smithy.utils.StringUtils;

/**
 * There are certain assumptions we can/have to make about
 * Types from the AWS SDK for Java V1 libraries.
 */
public class AwsSdkNativeV1 extends Native {

    public AwsSdkNativeV1(final ServiceShape serviceShape,
                          final Model model) {
        super(packageNameForAwsSdkV1Shape(serviceShape),
                serviceShape,
                model,
                defaultModelPackageName(packageNameForAwsSdkV1Shape(serviceShape))
        );
        checkForAwsServiceConstants();
    }

    // The values of these maps are NOT in smithy models and thus must be hard-coded
    private static final Map<String, String> AWS_SERVICE_NAMESPACE_TO_CLIENT_INTERFACE;
    private static final Map<String, String> AWS_SERVICE_NAMESPACE_TO_BASE_EXCEPTION;

    static {
        // These are NOT in the service's model package
        // i.e: kms : com.amazonaws.kms.AWSKMS
        AWS_SERVICE_NAMESPACE_TO_CLIENT_INTERFACE = Map.ofEntries(
                Map.entry("com.amazonaws.kms", "AWSKMS"),
                Map.entry("com.amazonaws.dynamodb", "AmazonDynamoDB"),
                Map.entry("com.amazonaws.s3", "AmazonS3")
        );
        // These are in the service's model package
        // i.e.: kms : com.amazonaws.kms.model.AWSKMSException
        AWS_SERVICE_NAMESPACE_TO_BASE_EXCEPTION = Map.ofEntries(
                Map.entry("com.amazonaws.kms", "AWSKMSException"),
                Map.entry("com.amazonaws.dynamodb", "AmazonDynamoDBException"),
                Map.entry("com.amazonaws.s3", "AmazonS3Exception")
        );
    }

    /** Validates that Polymorph knows non-smithy modeled constants for an AWS Service */
    private void checkForAwsServiceConstants() {
        String namespace = serviceShape.getId().getNamespace();
        boolean knowBaseException = AWS_SERVICE_NAMESPACE_TO_BASE_EXCEPTION.containsKey(namespace);
        if (!knowBaseException) {
            throw new IllegalArgumentException(
                    "Polymorph does not know this service's Base Exception: %s".formatted(namespace));
        }
        boolean knowClientInterface = AWS_SERVICE_NAMESPACE_TO_CLIENT_INTERFACE.containsKey(namespace);
        if (!knowClientInterface) {
            throw new IllegalArgumentException(
                    "Polymorph does not know this service's Client Interface: %s".formatted(namespace));
        }
    }

    /**
     * Throws IllegalArgumentException if shapeId is not in namespace
     */
    private void checkInServiceNamespace(final ShapeId shapeId) {
        if (!isInServiceNameSpace(shapeId)) {
            throw new IllegalArgumentException(
                    "ShapeId %s is not in this namespace %s".formatted(
                            shapeId, serviceShape.getId().getNamespace()));
        }
    }

    @Override
    public ClassName typeForStructure(final Shape shape) {
        if (!(shape.isUnionShape() || shape.isStructureShape())) {
            throw new IllegalArgumentException(
                    "typeForStructure should only be called for Structures or Unions. ShapeId: %s"
                            .formatted(shape.getId()));
        }
        if (shape.hasTrait(TraitDefinition.class)) {
            throw new IllegalArgumentException(
                    "Trait definition structures have no corresponding generated type");
        }
        // check if this Shape is in AWS SDK for Java V1 package
        if (AwsSdkNameResolverHelpers.isAwsSdkServiceId(shape.getId())) {
            // Assume that the shape is in the model package
            return ClassName.get(
                    defaultModelPackageName(packageNameForAwsSdkV1Shape(shape)),
                    StringUtils.capitalize(shape.getId().getName()));
        }
        return super.typeForStructure(shape);
    }

    /** The AWS SDK for Java V1 replaces
     *  the last 'Response' with 'Result'
     *  in operation outputs.
     */
    public TypeName typeForOperationOutput(final ShapeId shapeId) {
        StructureShape shape = model.expectShape(shapeId, StructureShape.class);
        ClassName smithyName = typeForStructure(shape);
        // TODO: handle AWS SDK v2 naming convention, which uses 'Response', not 'Result'
        if (smithyName.simpleName().endsWith("Response")) {
            return ClassName.get(smithyName.packageName(),
                    smithyName.simpleName()
                            .substring(
                                    0,
                                    smithyName.simpleName().lastIndexOf("Response"))
                            + "Result"
            );
        }
        return smithyName;
    }

    /**
     * Returns the TypeName for an AWS Service's Client Interface.
     */
    @Override
    public ClassName typeForService(final ServiceShape shape) {
        //TODO: refactor to not throw error on other namespace,
        // but instead check AWS_SERVICE_NAMESPACE_TO_CLIENT_INTERFACE for
        // namespace, and throw exception if not found.
        checkInServiceNamespace(shape.getId());
        return ClassName.get(
                packageName,
                AWS_SERVICE_NAMESPACE_TO_CLIENT_INTERFACE.get(
                        serviceShape.getId().getNamespace()));
    }

    /**
     * Returns the TypeName for an AWS Service's Base Exception.
     * <p>
     * To be clear, a Base Exception is concrete.
     * But all of a service's other exceptions extend it.
     */
    public TypeName baseErrorForService() {
        return ClassName.get(
                modelPackage,
                AWS_SERVICE_NAMESPACE_TO_BASE_EXCEPTION.get(
                        serviceShape.getId().getNamespace()));
    }

    public static String packageNameForService(final String awsServiceName) {
        String rtn = awsServiceName;
        if (awsServiceName.equals("dynamodb")) {
            rtn = "dynamodbv2";
        }
        return "com.amazonaws.services.%s".formatted(rtn);
    }

    static String packageNameForAwsSdkV1Shape(final Shape shape) {
        String awsServiceName = AwsSdkNameResolverHelpers.awsServiceNameFromShape(shape);
        return packageNameForService(awsServiceName);
    }

    public static String defaultModelPackageName(final String packageName) {
        return "%s.model".formatted(packageName);
    }

}
