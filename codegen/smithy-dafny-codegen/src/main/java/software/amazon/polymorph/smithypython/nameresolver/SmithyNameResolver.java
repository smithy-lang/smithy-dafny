package software.amazon.polymorph.smithypython.nameresolver;

import java.util.HashSet;
import java.util.Locale;
import java.util.Set;
import java.util.stream.Collectors;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.codegen.core.CodegenContext;
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
 * to useful strings used in Smithy-Python generated code.
 */
public class SmithyNameResolver {

  public static String clientForService(ServiceShape serviceShape) {
      if (serviceShape.hasTrait(LocalServiceTrait.class)) {
          return serviceShape.expectTrait(LocalServiceTrait.class).getSdkId() + "Client";
      } else {
          throw new UnsupportedOperationException("Non-local services not supported");
      }
  }

  public static String shimForService(ServiceShape serviceShape) {
      if (serviceShape.hasTrait(LocalServiceTrait.class)) {
          return serviceShape.expectTrait(LocalServiceTrait.class).getSdkId() + "Shim";
      } else {
          throw new UnsupportedOperationException("Non-local services not supported");
      }
  }

  public static String getPythonModuleNamespaceForSmithyNamespace(String smithyNamespace) {
    return smithyNamespace.toLowerCase(Locale.ROOT).replace(".", "_");
  }

  public static String getSmithyGeneratedModelLocationForShape(Shape shape,
      GenerationContext codegenContext) {
    return getSmithyGeneratedModelLocationForShapeId(shape.getId(), codegenContext);
  }

  /**
   * For a given ShapeId, returns a String representing the path where that shape is generated.
   * The return value can be directly used to import that shape; e.g.
   *   `from {returnValue} import {my_shape.getId()}`
   * @param shapeId
   * @param codegenContext
   * @return
   */
  public static String getSmithyGeneratedModelLocationForShapeId(ShapeId shapeId,
      GenerationContext codegenContext) {
    String moduleNamespace = getSmithyGeneratedModuleNamespaceForSmithyNamespace(shapeId.getNamespace(),
        codegenContext);
    String moduleFilename = getSmithyGeneratedModuleFilenameForSmithyShape(shapeId, codegenContext);
    return moduleNamespace + moduleFilename;
  }

  public static void importSmithyGeneratedTypeForShape(PythonWriter writer, Shape shape,
      GenerationContext codegenContext) {
    importSmithyGeneratedTypeForShape(writer, shape.getId(), codegenContext);
  }

  /**
   * For a given ShapeId and PythonWriter, writes an import for the corresponding generated shape.
   * @param shapeId
   * @param codegenContext
   * @param writer
   */
  public static void importSmithyGeneratedTypeForShape(PythonWriter writer, ShapeId shapeId,
      GenerationContext codegenContext) {
    writer.addImport(
        SmithyNameResolver.getSmithyGeneratedModelLocationForShapeId(
            shapeId, codegenContext
        ),
        shapeId.getName()
    );
  }

  /**
   * For any ShapeId, returns the filename inside `.smithygenerated`
   *   where that Shape is generated.
   * @param shapeId
   * @param codegenContext
   * @return
   */
  private static String getSmithyGeneratedModuleFilenameForSmithyShape(ShapeId shapeId,
      GenerationContext codegenContext) {
    Shape shape = codegenContext.model().expectShape(shapeId);
    if (shape.hasTrait(ReferenceTrait.class)
        && shape.isServiceShape()
        && shape.hasTrait(LocalServiceTrait.class)) {
      // LocalService clients are generated at `my_module.smithygenerated.client`
      return ".client";
    }
    else if (shape.hasTrait(ErrorTrait.class)) {
      return ".errors";
    } else {
      return ".models";
    }
  }

  public static String getSmithyGeneratedTypeForUnion(UnionShape unionShape,
      MemberShape memberShape) {
    return unionShape.getId().getName() + memberShape.getMemberName();
  }

  public static void importSmithyGeneratedTypeForUnion(PythonWriter writer,
      GenerationContext context, UnionShape unionShape, MemberShape memberShape) {
    writer.addImport(
        getSmithyGeneratedModelLocationForShapeId(unionShape.getId(), context),
        getSmithyGeneratedTypeForUnion(unionShape, memberShape)
    );
  }

  /**
   * Given the namespace of a Smithy shape, returns a Pythonic access path to the namespace
   * that can be used to import shapes from the namespace.
   * @param smithyNamespace
   * @param codegenContext
   * @return
   */
  public static String getSmithyGeneratedModuleNamespaceForSmithyNamespace(String smithyNamespace,
      GenerationContext codegenContext) {
    return
        getPythonModuleNamespaceForSmithyNamespace(smithyNamespace)
            .contains(codegenContext.settings().getModuleName())
        // If the provided namespace is the current namespace (i.e. the module being generated),
        // return an empty string, as "." represents the current module
        ? ""
        // If the provided namespace is not the current namespace (i.e. a dependency namespace),
        // return the other namespace's smithygenerated module;
        // i.e. `other_module.smithygenerated`
        :  getPythonModuleNamespaceForSmithyNamespace(smithyNamespace) + ".smithygenerated";
  }

  public static String getSmithyGeneratedConfigFilepathForSmithyNamespace(String smithyNamespace,
      GenerationContext codegenContext) {
    return getSmithyGeneratedModuleNamespaceForSmithyNamespace(smithyNamespace, codegenContext)
        + ".config";
  }

  static Set<ShapeId> localServiceConfigShapes = new HashSet<>();

  public static Set<ShapeId> getLocalServiceConfigShapes(CodegenContext codegenContext) {

    if (localServiceConfigShapes.isEmpty()) {
      localServiceConfigShapes =  codegenContext.model().getServiceShapes().stream()
          .map(serviceShape1 -> serviceShape1.expectTrait(LocalServiceTrait.class))
          .map(localServiceTrait -> localServiceTrait.getConfigId())
          .collect(Collectors.toSet());
    }
    return localServiceConfigShapes;
  }
}
