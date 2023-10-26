package software.amazon.polymorph.smithypython.awssdk.nameresolver;

import java.util.Locale;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.Utils;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonWriter;

/**
 * Contains utility functions that map Smithy shapes
 * to useful strings used in Smithy-Python generated AWS SDK code.
 */
public class AwsSdkNameResolver {

  public static boolean isAwsSdkShape(Shape shape) {
    return isAwsSdkShape(shape.getId());
  }

  public static boolean isAwsSdkShape(ShapeId shapeId) {
    // If the shape namespace is not in our list of known SDK namespaces,
    // it is not a (known) SDK namespace
    return !resolveAwsSdkSmithyModelNamespaceToDafnyExternNamespace(shapeId.getNamespace())
        .equals(shapeId.getNamespace());
  }

  /**
   * Returns the name of the Smithy-generated shim for the provided AWS SDK serviceShape.
   * The serviceShape SHOULD be an AWS SDK.
   * ex. example.namespace.ExampleService -> "ExampleServiceShim"
   * @param serviceShape
   * @return
   */
  public static String shimForService(ServiceShape serviceShape) {
    if ("TrentService".equals(serviceShape.getId().getName())) {
      return "KMSClientShim";
    }

    return serviceShape.getId().getName() + "Shim";
  }

  /**
   * Resolve the provided smithyNamespace to its corresponding Dafny Extern namespace.
   * Our Dafny code declares an extern namespace independent of the Smithy namespace;
   *   this function maps the two namespaces.
   * @param smithyNamespace
   * @return
   */
  public static String resolveAwsSdkSmithyModelNamespaceToDafnyExternNamespace(String smithyNamespace) {
    return switch (smithyNamespace) {
      case "com.amazonaws.kms" -> "software.amazon.cryptography.services.kms";
      case "com.amazonaws.dynamodb" -> "software.amazon.cryptography.services.dynamodb";
      default -> smithyNamespace;
    };
  }

  /**
   * Returns the name of the function that converts the provided shape's Dafny-modelled type
   *   to the corresponding AWS SDK-modelled type.
   * This function will be defined in the `dafny_to_aws_sdk.py` file.
   * ex. example.namespace.ExampleShape -> "DafnyToAwsSdk_example_namespace_ExampleShape"
   * @param shape
   * @return
   */
  public static String getDafnyToAwsSdkFunctionNameForShape(Shape shape) {
    return "DafnyToAwsSdk_"
        + SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(shape.getId().getNamespace())
        + "_" + shape.getId().getName();
  }

  /**
   * Returns the name of the function that converts the provided shape's AWS SDK-modelled type
   *   to the corresponding Dafny-modelled type.
   * This function will be defined in the `aws_sdk_to_dafny.py` file.
   * ex. example.namespace.ExampleShape -> "AwsSdkToDafny_example_namespace_ExampleShape"
   * @param shape
   * @return
   */
  public static String getAwsSdkToDafnyFunctionNameForShape(Shape shape) {
    return "AwsSdkToDafny_"
        + SmithyNameResolver.getPythonModuleNamespaceForSmithyNamespace(shape.getId().getNamespace())
        + "_" + shape.getId().getName();
  }}
