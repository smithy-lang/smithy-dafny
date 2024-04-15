// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
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

  // TODO: similar smarts to capitalize known words ala DotNetNameResolver.capitalizeNamespaceSegment
  // See https://smithy.io/2.0/aws/aws-core.html#using-sdk-service-id-for-client-naming
  public static String mungeSdkId(String sdkId) {
    return StringUtils.capitalize(sdkId.replace(" ", ""));
  }

  // TODO Accept a Shape and check if it is in the closure
  // of a service with the @aws.api#service trait instead
  public static boolean isInAwsSdkNamespace(ShapeId shapeId) {
    return shapeId.getNamespace().startsWith("com.amazonaws.");
  }

  // TODO: This should be 100% derived from the service name,
  // (determined by the shape name or the aws.api#service$sdkId value)
  // so I belive we should be able to drop this method.
  public static String awsServiceNameFromShape(final Shape shape) {
    String[] namespaceParts = shape.getId().getNamespace().split("\\.");
    return namespaceParts[namespaceParts.length - 1];
  }

  public static ServiceShape getAwsServiceShape(
    final Model model,
    final ShapeId shapeId
  ) {
    if (!isInAwsSdkNamespace(shapeId)) throw new IllegalStateException(
      "Shape is not in an AWS SKD namespace:" +
      shapeId.getName() +
      ", " +
      shapeId.getNamespace()
    );

    return ModelUtils.serviceFromNamespace(model, shapeId.getNamespace());
  }
}
