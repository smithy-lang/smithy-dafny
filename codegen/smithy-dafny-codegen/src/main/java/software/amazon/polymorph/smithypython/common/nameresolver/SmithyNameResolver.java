// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.common.nameresolver;

import java.util.HashSet;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.codegen.core.CodegenContext;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.Shape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.UnionShape;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonSettings;
import software.amazon.smithy.python.codegen.PythonWriter;

/**
 * Contains utility functions that map Smithy shapes to useful strings used in Smithy-Python
 * generated code. i.e. strings in this file match behavior of Smithy-Python- (or
 * Smithy-Dafny-Python-) generated code
 */
public class SmithyNameResolver {

  // Cached set of
  static Set<ShapeId> localServiceConfigShapes = new HashSet<>();
  // Map from a Smithy service namespace (as a string) to its wrapping Python module name.
  // This is passed into Smithy-Dafny, which passes it into Python codegen.
  private static Map<String, String> smithyNamespaceToPythonModuleNameMap;

  /**
   * Returns a set of serviceShapes in the model that have the `@aws.polymorph#localService` trait.
   *
   * @param codegenContext
   * @return
   */
  public static Set<ShapeId> getLocalServiceConfigShapes(CodegenContext codegenContext) {

    return getLocalServiceConfigShapes(codegenContext.model());
  }

  /**
   * Retrieve set of localService config shapes; if the set has not been retrieved yet, search the
   * model to populate the set.
   *
   * @param model
   * @return
   */
  public static Set<ShapeId> getLocalServiceConfigShapes(Model model) {

    if (localServiceConfigShapes.isEmpty()) {
      localServiceConfigShapes =
          model.getServiceShapes().stream()
              .filter(serviceShape -> serviceShape.hasTrait(LocalServiceTrait.class))
              .map(serviceShape -> serviceShape.expectTrait(LocalServiceTrait.class))
              .map(localServiceTrait -> localServiceTrait.getConfigId())
              .collect(Collectors.toSet());
    }
    return localServiceConfigShapes;
  }

  public static void setSmithyNamespaceToPythonModuleNameMap(
      Map<String, String> smithyNamespaceToPythonModuleNameMap) {
    SmithyNameResolver.smithyNamespaceToPythonModuleNameMap = smithyNamespaceToPythonModuleNameMap;
  }

  public static String getPythonModuleNameForSmithyNamespace(String smithyNamespace) {
    return smithyNamespaceToPythonModuleNameMap.get(smithyNamespace);
  }

  /**
   * Returns the name of the Smithy-generated client for the provided serviceShape. The serviceShape
   * SHOULD be a localService. ex. example.namespace.ExampleService -> "ExampleServiceClient"
   *
   * @param serviceShape
   * @return
   */
  public static String clientForService(ServiceShape serviceShape) {
    if (serviceShape.hasTrait(LocalServiceTrait.class)) {
      return serviceShape.expectTrait(LocalServiceTrait.class).getSdkId() + "Client";
    } else {
      throw new UnsupportedOperationException("Non-local services not supported");
    }
  }

  /**
   * Returns the name of the Smithy-generated shim for the provided serviceShape. The serviceShape
   * SHOULD be a localService. ex. example.namespace.ExampleService -> "ExampleServiceShim"
   *
   * @param serviceShape
   * @return
   */
  public static String shimForService(ServiceShape serviceShape) {
    if (serviceShape.hasTrait(LocalServiceTrait.class)) {
      return serviceShape.expectTrait(LocalServiceTrait.class).getSdkId() + "Shim";
    } else {
      throw new UnsupportedOperationException("Non-local services not supported");
    }
  }

  /**
   * Returns the name of the Python module containing Smithy code for the provided smithyNamespace.
   * ex. example.namespace -> "example_namespace"
   *
   * @param smithyNamespace
   * @return
   */
  public static String getServiceSmithygeneratedDirectoryNameForNamespace(String smithyNamespace) {
    return smithyNamespace.toLowerCase(Locale.ROOT).replace(".", "_");
  }

  /**
   * For a given ShapeId, returns a String representing the path where that shape is generated. The
   * return value can be directly used to import that shape; e.g. `from {returnValue} import
   * {my_shape.getId()}`
   *
   * @param shape
   * @param codegenContext
   * @return
   */
  public static String getSmithyGeneratedModelLocationForShape(
      Shape shape, GenerationContext codegenContext) {
    return getSmithyGeneratedModelLocationForShape(shape.getId(), codegenContext);
  }

  /**
   * For a given ShapeId, returns a String representing the path where that shape is generated. The
   * return value can be directly used to import that shape; e.g. `from {returnValue} import
   * {my_shape.getId()}`
   *
   * @param shapeId
   * @param codegenContext
   * @return
   */
  public static String getSmithyGeneratedModelLocationForShape(
      ShapeId shapeId, GenerationContext codegenContext) {
    String moduleNamespace =
        getPythonModuleSmithygeneratedPathForSmithyNamespace(
            shapeId.getNamespace(), codegenContext);
    String moduleFilename = getSmithyGeneratedModuleFilenameForSmithyShape(shapeId, codegenContext);
    return moduleNamespace + moduleFilename;
  }

  /**
   * For a given ShapeId and PythonWriter, writes an import for the corresponding generated shape.
   * ex. example.namespace.ExampleShape -> "from example_namespace.smithygenerated.[file] import
   * ExampleShape"
   *
   * @param shape
   * @param codegenContext
   * @param writer
   */
  public static void importSmithyGeneratedTypeForShape(
      PythonWriter writer, Shape shape, GenerationContext codegenContext) {
    importSmithyGeneratedTypeForShape(writer, shape.getId(), codegenContext);
  }

  /**
   * For a given ShapeId and PythonWriter, writes an import for the corresponding generated shape.
   * ex. example.namespace.ExampleShape -> "from example_namespace.smithygenerated.[file] import
   * ExampleShape"
   *
   * @param shapeId
   * @param codegenContext
   * @param writer
   */
  public static void importSmithyGeneratedTypeForShape(
      PythonWriter writer, ShapeId shapeId, GenerationContext codegenContext) {
    writer.addStdlibImport(
        SmithyNameResolver.getSmithyGeneratedModelLocationForShape(shapeId, codegenContext));
  }

  /**
   * For any ShapeId, returns the filename inside `.smithygenerated` where that Shape is generated.
   *
   * @param shape
   * @param codegenContext
   * @return
   */
  public static String getSmithyGeneratedModuleFilenameForSmithyShape(
      Shape shape, GenerationContext codegenContext) {
    return getSmithyGeneratedModuleFilenameForSmithyShape(shape.getId(), codegenContext);
  }

  /**
   * For any ShapeId, returns the filename inside `.smithygenerated` where that Shape is generated.
   *
   * @param shapeId
   * @param codegenContext
   * @return
   */
  public static String getSmithyGeneratedModuleFilenameForSmithyShape(
      ShapeId shapeId, GenerationContext codegenContext) {
    Shape shape = codegenContext.model().expectShape(shapeId);
    if (shape.hasTrait(ReferenceTrait.class)
        && shape.isServiceShape()
        && shape.hasTrait(LocalServiceTrait.class)) {
      // LocalService clients are generated at `my_module.smithygenerated.client`
      return ".client";
    } else if (shape.hasTrait(ErrorTrait.class)) {
      return ".errors";
    } else if (getLocalServiceConfigShapes(codegenContext).contains(shapeId)) {
      return ".config";
    } else if (shape.hasTrait(ReferenceTrait.class)) {
      return ".references";
    } else {
      return ".models";
    }
  }

  /**
   * Returns the name of the Smithy-generated type for the provided UnionShape and corresponding
   * union value as its MemberShape. ex. example.namespace.ExampleUnion:ExampleMember ->
   * "ExampleUnionExampleMember"
   *
   * @param unionShape
   * @param memberShape
   * @return
   */
  public static String getSmithyGeneratedTypeForUnion(
      UnionShape unionShape, MemberShape memberShape) {
    return unionShape.getId().getName() + memberShape.getMemberName();
  }

  /**
   * Given the namespace of a Smithy shape, returns a Pythonic access path to the namespace that can
   * be used to import shapes from its `smithygenerated` namespace.
   *
   * @param smithyNamespace
   * @param codegenContext
   * @return
   */
  public static String getPythonModuleSmithygeneratedPathForSmithyNamespace(
      String smithyNamespace, GenerationContext codegenContext) {
    return getPythonModuleSmithygeneratedPathForSmithyNamespace(
        smithyNamespace, codegenContext.settings());
  }

  /**
   * Given the namespace of a Smithy shape, returns a Pythonic access path to the namespace that can
   * be used to import shapes from its Smithy-generated namespace.
   *
   * @param smithyNamespace
   * @param settings
   * @return
   */
  public static String getPythonModuleSmithygeneratedPathForSmithyNamespace(
      String smithyNamespace, PythonSettings settings) {
    String pythonModuleName;
    String namespace;
    // `smithy.api.Unit:`
    // Smithy-Dafny will generate a stand-in shape in the service
    if ("smithy.api".equals(smithyNamespace)) {
      pythonModuleName = settings.getModuleName();
      namespace = settings.getService().getNamespace();
    } else {
      pythonModuleName = getPythonModuleNameForSmithyNamespace(smithyNamespace);
      namespace = smithyNamespace;
    }
    return pythonModuleName + ".smithygenerated." + getServiceSmithygeneratedDirectoryNameForNamespace(namespace);
  }

  /**
   * Returns the name of the function that converts the provided shape's Dafny-modelled type to the
   * corresponding Smithy-modelled type. This function will be defined in the `dafny_to_smithy.py`
   * file. ex. example.namespace.ExampleShape -> "DafnyToSmithy_example_namespace_ExampleShape"
   *
   * @param shape
   * @return
   */
  public static String getDafnyToSmithyFunctionNameForShape(
      Shape shape, GenerationContext context) {
    return "DafnyToSmithy_"
        + SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
            shape.getId().getNamespace())
        + "_"
        + shape.getId().getName();
  }

  /**
   * Returns the name of the function that converts the provided shape's Smithy-modelled type to the
   * corresponding Dafny-modelled type. This function will be defined in the `smithy_to_dafny.py`
   * file. ex. example.namespace.ExampleShape -> "SmithyToDafny_example_namespace_ExampleShape"
   *
   * @param shape
   * @return
   */
  public static String getSmithyToDafnyFunctionNameForShape(
      Shape shape, GenerationContext context) {
    return "SmithyToDafny_"
        + SmithyNameResolver.getServiceSmithygeneratedDirectoryNameForNamespace(
            shape.getId().getNamespace())
        + "_"
        + shape.getId().getName();
  }
}
