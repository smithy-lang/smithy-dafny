package software.amazon.polymorph.smithyjava.nameresolver;

import com.squareup.javapoet.ClassName;
import com.squareup.javapoet.TypeName;

import org.slf4j.Logger;
import org.slf4j.LoggerFactory;

import java.util.Map;

import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.TraitDefinition;
import software.amazon.smithy.utils.StringUtils;

/**
 * There are certain assumptions we can/have to make about
 * Types from the AWS SDK for Java libraries.
 */
public class AwsSdkNative extends Native {
    private static final Logger LOGGER = LoggerFactory.getLogger(AwsSdkNative.class);
    private final String awsServiceName;

    public AwsSdkNative(final ServiceShape serviceShape,
                        final Model model) {
        super(packageNameForServiceShape(serviceShape), serviceShape, model,
                defaultModelPackageName(packageNameForServiceShape(serviceShape)));
        awsServiceName = awsServiceNameFromServiceShape(serviceShape);
    }

    private static final Map<String, String> AWS_SERVICE_NAMESPACE_TO_CLIENT_IMPL;
    private static final Map<String, String> AWS_SERVICE_NAMESPACE_TO_CLIENT_INTERFACE;
    private static final Map<String, String> AWS_SERVICE_NAMESPACE_TO_BASE_EXCEPTION;

    static {
        // These are NOT in the service's model package
        AWS_SERVICE_NAMESPACE_TO_CLIENT_IMPL = Map.ofEntries(
                Map.entry("com.amazonaws.kms", "AWSKMSClient"),
                Map.entry("com.amazonaws.dynamodb", "AmazonDynamoDBClient"),
                Map.entry("com.amazonaws.s3", "AmazonS3Client")
        );
        // These are NOT in the service's model package
        AWS_SERVICE_NAMESPACE_TO_CLIENT_INTERFACE = Map.ofEntries(
                Map.entry("com.amazonaws.kms", "AWSKMS"),
                Map.entry("com.amazonaws.dynamodb", "AmazonDynamoDB"),
                Map.entry("com.amazonaws.s3", "AmazonS3")
        );
        // These are in the service's model package
        AWS_SERVICE_NAMESPACE_TO_BASE_EXCEPTION = Map.ofEntries(
                Map.entry("com.amazonaws.kms", "AWSKMSException"),
                Map.entry("com.amazonaws.dynamodb", "AmazonDynamoDBException"),
                Map.entry("com.amazonaws.s3", "AmazonS3Exception")
        );
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

    public boolean isInServiceNameSpace(final ShapeId shapeId) {
        return shapeId.getNamespace().contains(serviceShape.getId().getNamespace());
    }

    @Override
    public ClassName typeForStructure(final StructureShape shape) {
        if (shape.hasTrait(TraitDefinition.class)) {
            throw new IllegalArgumentException(
                    "Trait definition structures have no corresponding generated type");
        }
        checkInServiceNamespace(shape.getId());
        return ClassName.get(modelPackage, StringUtils.capitalize(shape.getId().getName()));
    }

    /** The AWS SDK for Java replaces
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
    public TypeName typeForService(final ServiceShape shape) {
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

    static String awsServiceNameFromServiceShape(final ServiceShape serviceShape) {
        String[] namespaceParts = serviceShape.getId().getNamespace().split("\\.");
        return namespaceParts[namespaceParts.length - 1];
    }

    static String packageNameForServiceShape(final ServiceShape serviceShape) {
        String awsServiceName = awsServiceNameFromServiceShape(serviceShape);
        return packageNameForService(awsServiceName);
    }

    public static String defaultModelPackageName(final String packageName) {
        return "%s.model".formatted(packageName);
    }

}
