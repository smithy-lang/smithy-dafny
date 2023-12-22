// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.awssdk.nameresolver;

import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;

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
   * Returns the name of the Smithy-generated shim for the provided AWS SDK serviceShape. The
   * serviceShape SHOULD be an AWS SDK. This also standardizes some "legacy" service names. ex.
   * example.namespace.ExampleService -> "ExampleServiceShim"
   *
   * @param serviceShape
   * @return
   */
  public static String shimForService(ServiceShape serviceShape) {
    return switch (serviceShape.getId().getName()) {
      case "TrentService" -> "KMSClientShim";
      case "DynamoDB_20120810" -> "DynamoDBClientShim";
      default -> serviceShape.getId().getName();
    };
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
   * file. ex. example.namespace.ExampleShape -> "DafnyToAwsSdk_example_namespace_ExampleShape"
   * @param shape
   * @return
   */
  public static String getDafnyToAwsSdkFunctionNameForShape(Shape shape) {
    return "DafnyToAwsSdk_"
        + SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(
            shape.getId().getNamespace())
        + "_"
        + shape.getId().getName();
  }

  /**
   * Returns the name of the function that converts the provided shape's AWS SDK-modelled type to
   * the corresponding Dafny-modelled type. This function will be defined in the
   * `aws_sdk_to_dafny.py` file. ex. example.namespace.ExampleShape ->
   * "AwsSdkToDafny_example_namespace_ExampleShape"
   *
   * @param shape
   * @return
   */
  public static String getAwsSdkToDafnyFunctionNameForShape(Shape shape) {
    return "AwsSdkToDafny_"
        + SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(
            shape.getId().getNamespace())
        + "_"
        + shape.getId().getName();
  }
}
