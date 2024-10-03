// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.awssdk.nameresolver;

import com.google.common.base.CaseFormat;
import software.amazon.polymorph.smithydafny.DafnyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.utils.CaseUtils;

/**
 * Contains utility functions that map Smithy shapes to useful strings used in Smithy-Python
 * generated AWS SDK code.
 */
public class AwsSdkNameResolver {

  public static boolean isAwsSdkShape(Shape shape) {
    return isAwsSdkShape(shape.getId());
  }

  /**
   * Returns true if the shape is in an AWS SDK service namespace.
   * @param shapeId
   * @return
   */
  public static boolean isAwsSdkShape(ShapeId shapeId) {
    // If the shape namespace is not in our list of known SDK namespaces,
    // it is not a (known) SDK namespace
    return isAwsSdkNamespace(shapeId.getNamespace());
  }

  /**
   * Returns true if the namespace represents an AWS SDK service namespace.
   * @param namespace
   * @return
   */
  public static boolean isAwsSdkNamespace(String namespace) {
    return namespace.startsWith("com.amazonaws");
  }

  /**
   * Returns the type name of the client for the provided AWS SDK serviceShape.
   * This also standardizes some "legacy" service names.
   * When setting up a new AWS service with Smithy-Dafny,
   * this logic will need to be extended to support that service.
   *
   * @param serviceShape
   * @return
   */
  public static String clientNameForService(ServiceShape serviceShape) {
    if (!isAwsSdkNamespace(serviceShape.getId().getNamespace())) {
      throw new IllegalArgumentException(
        "serviceShape is not an AWS SDK service: " + serviceShape
      );
    }
    return switch (serviceShape.getId().getName()) {
      case "TrentService" -> "KMSClient";
      case "DynamoDB_20120810" -> "DynamoDBClient";
      default -> serviceShape.getId().getName();
    };
  }

  /**
   * Returns the name of the Smithy-generated shim for the provided AWS SDK serviceShape. The
   * serviceShape SHOULD be an AWS SDK.
   *
   * @param serviceShape
   * @return
   */
  public static String shimNameForService(ServiceShape serviceShape) {
    return clientNameForService(serviceShape) + "Shim";
  }

  /**
   * Returns the name of the error type that wraps AWS SDK errors.
   * Customers may see this error type, so it should be reasonably informative.
   *
   * @param serviceShape
   * @return
   */
  public static String dependencyErrorNameForService(
    ServiceShape serviceShape
  ) {
    return DafnyNameResolver.dafnyBaseModuleName(
      serviceShape.getId().getNamespace()
    );
  }

  /**
   * Returns the name of the function that converts the provided shape's Dafny-modelled type to the
   * corresponding AWS SDK-modelled type. This function will be defined in the `dafny_to_aws_sdk.py`
   * file. ex. example.namespace.ExampleShape -> "example_namespace_ExampleShape"
   *
   * @param shape
   * @return
   */
  public static String getDafnyToAwsSdkFunctionNameForShape(Shape shape) {
    return getConversionFunctionNameForShape(shape);
  }

  /**
   * Returns the name of the function that converts the provided shape's AWS SDK-modelled type to
   * the corresponding Dafny-modelled type. This function will be defined in the
   * `aws_sdk_to_dafny.py` file. ex. example.namespace.ExampleShape ->
   * "example_namespace_ExampleShape"
   *
   * @param shape
   * @return
   */
  public static String getAwsSdkToDafnyFunctionNameForShape(Shape shape) {
    return getConversionFunctionNameForShape(shape);
  }

  /**
   * Returns the function name to use when converting the shape between boto/Dafny types.
   * @param shape
   * @return
   */
  public static String getConversionFunctionNameForShape(Shape shape) {
    return (
      SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
        shape.getId().getNamespace()
      ) +
      "_" +
      shape.getId().getName()
    );
  }
}
