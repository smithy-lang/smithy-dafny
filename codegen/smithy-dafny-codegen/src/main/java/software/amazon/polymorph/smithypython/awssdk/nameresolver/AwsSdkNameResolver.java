// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.awssdk.nameresolver;

import com.google.common.base.CaseFormat;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.utils.CaseUtils;

/**
 * Contains utility functions that map Smithy shapes to useful strings used in Smithy-Python
 * generated AWS SDK code.
 */
public class AwsSdkNameResolver {

  public static boolean isAwsSdkShape(Shape shape) {
    return isAwsSdkShape(shape.getId());
  }

  public static boolean isAwsSdkShape(ShapeId shapeId) {
    // If the shape namespace is not in our list of known SDK namespaces,
    // it is not a (known) SDK namespace
    return shapeId.getNamespace().startsWith("com.amazonaws");
  }

  /**
   * Returns the type name of the client for the provided AWS SDK serviceShape. The
   * serviceShape SHOULD be an AWS SDK. This also standardizes some "legacy" service names.
   *
   * @param serviceShape
   * @return
   */
  public static String clientNameForService(ServiceShape serviceShape) {
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
  public static String dependencyErrorNameForService(ServiceShape serviceShape) {
    if (serviceShape.getId().getNamespace().toLowerCase().contains("keystore")) {
      System.out.println(CaseUtils.toPascalCase(serviceShape.getId().getNamespace().replace(".", "_")));
      System.out.println(CaseFormat.UPPER_CAMEL.to(CaseFormat.UPPER_UNDERSCORE, serviceShape.getId().getNamespace()));
    }
    return CaseUtils.toPascalCase(serviceShape.getId().getNamespace().replace(".", "_"));
  }

  /**
   * Resolve the provided smithyNamespace to its corresponding Dafny Extern namespace. Our Dafny
   * code declares an extern namespace independent of the Smithy namespace; this function maps the
   * two namespaces.
   *
   * @param smithyNamespace
   * @return
   */
  public static String resolveAwsSdkSmithyModelNamespaceToDafnyExternNamespace(
      String smithyNamespace) {
    String rtn = smithyNamespace.toLowerCase();
    if (smithyNamespace.startsWith("aws")) {
      rtn = rtn.replaceFirst("aws", "software.amazon");
    } else if (smithyNamespace.startsWith("com.amazonaws")) {
      rtn = rtn.replaceFirst("com.amazonaws", "software.amazon.cryptography.services");
    }
    return rtn;
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
    return SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
            shape.getId().getNamespace())
        + "_"
        + shape.getId().getName();
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
    return SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
            shape.getId().getNamespace())
        + "_"
        + shape.getId().getName();
  }
}
