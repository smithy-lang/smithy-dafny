// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice.extensions;

import java.util.Map;
import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.traits.JavaDocTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.polymorph.utils.ModelUtils;
import software.amazon.smithy.build.PluginContext;
import software.amazon.smithy.build.SmithyBuildPlugin;
import software.amazon.smithy.codegen.core.directed.CodegenDirector;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.AbstractShapeBuilder;
import software.amazon.smithy.model.shapes.EnumShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.traits.DocumentationTrait;
import software.amazon.smithy.model.traits.EnumTrait;
import software.amazon.smithy.model.transform.ModelTransformer;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonSettings;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.integration.PythonIntegration;
import software.amazon.smithy.utils.SmithyUnstableApi;

/**
 * Plugin to trigger Smithy-Dafny Python code generation.
 * This differs from the PythonClientCodegenPlugin by not calling
 *     runner.performDefaultCodegenTransforms();
 * and
 *     runner.createDedicatedInputsAndOutputs();
 * These methods transform the model in ways that the model does not align with
 *   the generated Dafny code.
 * This also transforms the model to bridge the gap between Polymorph-flavored Smithy and standard Smithy
 *   by mapping {@link JavaDocTrait}s to {@link DocumentationTrait}s
 *   and by adding {@link software.amazon.smithy.model.shapes.ResourceShape}s from {@link ReferenceTrait}s
 *   to the service shape so they can be discovered by Smithy plugins.
 */
@SmithyUnstableApi
public final class DafnyPythonLocalServiceClientCodegenPlugin
  implements SmithyBuildPlugin {

  public DafnyPythonLocalServiceClientCodegenPlugin(
    Map<String, String> smithyNamespaceToPythonModuleNameMap
  ) {
    super();
    SmithyNameResolver.setSmithyNamespaceToPythonModuleNameMap(
      smithyNamespaceToPythonModuleNameMap
    );
  }

  @Override
  public String getName() {
    return "dafny-python-localservice-client-codegen";
  }

  @Override
  public void execute(PluginContext context) {
    CodegenDirector<
      PythonWriter,
      PythonIntegration,
      GenerationContext,
      PythonSettings
    > runner = new CodegenDirector<>();

    PythonSettings settings = PythonSettings.from(context.getSettings());
    runner.settings(settings);
    runner.directedCodegen(new DirectedDafnyPythonLocalServiceCodegen());
    runner.fileManifest(context.getFileManifest());
    runner.integrationClass(PythonIntegration.class);

    ServiceShape serviceShape = context
      .getModel()
      .expectShape(settings.getService())
      .asServiceShape()
      .get();
    Model transformedModel = transformModelForLocalService(
      context.getModel(),
      serviceShape
    );

    runner.model(transformedModel);
    runner.service(settings.getService());

    runner.run();
  }

  /**
   * Perform all transformations on the model before running localService codegen.
   * @param model
   * @param serviceShape
   * @return
   */
  public static Model transformModelForLocalService(
    Model model,
    ServiceShape serviceShape
  ) {
    Model transformedModel = model;
    transformedModel =
      transformJavadocTraitsToDocumentationTraits(transformedModel);
    transformedModel =
      transformServiceShapeToAddReferenceResources(
        transformedModel,
        serviceShape
      );
    transformedModel = transformStringEnumShapesToEnumShapes(transformedModel);
    return transformedModel;
  }

  /**
   * For each object with a Polymorph {@link JavaDocTrait} containing documentation,
   * replace it with a new Smithy {@link DocumentationTrait} with that documentation.
   * Smithy plugins will generate docs for DocumentationTraits.
   * @param model
   * @return
   */
  public static Model transformJavadocTraitsToDocumentationTraits(Model model) {
    return ModelTransformer
      .create()
      .mapShapes(
        model,
        shape -> {
          if (shape.hasTrait(JavaDocTrait.class)) {
            JavaDocTrait javaDocTrait = shape
              .getTrait(JavaDocTrait.class)
              .get();
            DocumentationTrait documentationTrait = new DocumentationTrait(
              javaDocTrait.getValue()
            );

            AbstractShapeBuilder<?, ?> builder = ModelUtils.getBuilderForShape(
              shape
            );
            builder.addTrait(documentationTrait);
            return builder.build();
            // Crypto Tools developers sometimes write out long strings of slashes to mark a "break" in our smithy files
            // However, Smithy plugins interpret strings starting with `//` as a comment
            //   that becomes a DocumentationTrait!
            // This leads to poor UX on some pydocs.
            // Remove any DocumentationTraits consisting solely of `/`s.
          } else if (shape.hasTrait(DocumentationTrait.class)) {
            DocumentationTrait documentationTrait = shape
              .getTrait(DocumentationTrait.class)
              .get();
            String documentation = documentationTrait.getValue();

            if (documentation.trim().matches("/+")) {
              AbstractShapeBuilder<?, ?> builder =
                ModelUtils.getBuilderForShape(shape);
              builder.removeTrait(DocumentationTrait.ID);
              return builder.build();
            } else {
              return shape;
            }
          } else {
            return shape;
          }
        }
      );
  }

  /**
   * Smithy plugins require that resource shapes are attached to a ServiceShape.
   * Smithy plugins also do not understand Polymorph's {@link ReferenceTrait} and will not
   * discover the linked shape.
   * This parses Polymorph's ReferenceTrait to attach any referenced resources to the {@param serviceShape}
   * so the Smithy plugin's shape discovery can find the shape.
   * @param model
   * @param serviceShape
   * @return
   */
  public static Model transformServiceShapeToAddReferenceResources(
    Model model,
    ServiceShape serviceShape
  ) {
    ServiceShape.Builder transformedServiceShapeBuilder =
      serviceShape.toBuilder();
    ModelTransformer
      .create()
      .mapShapes(
        model,
        shape -> {
          if (shape.hasTrait(ReferenceTrait.class)) {
            ShapeId referenceShapeId = shape
              .expectTrait(ReferenceTrait.class)
              .getReferentId();
            if (model.expectShape(referenceShapeId).isResourceShape()) {
              transformedServiceShapeBuilder.addResource(referenceShapeId);
            }
          }
          return shape;
        }
      );

    return ModelTransformer
      .create()
      .mapShapes(
        model,
        shape -> {
          if (shape.getId().equals(serviceShape.getId())) {
            return transformedServiceShapeBuilder.build();
          } else {
            return shape;
          }
        }
      );
  }

  /**
   * Replace any StringShapes with EnumTraits
   * with StringShapes.
   * Smithy-Dafny Smithy usually model enums as StringShapes with EnumTraits,
   * but Smithy-Python will only generate native models for EnumShapes.
   * Replacing this lets Smithy-Dafny-Python plug in to Smithy-Python enum generation.
   * @param model
   * @return
   */
  public static Model transformStringEnumShapesToEnumShapes(Model model) {
    return ModelTransformer
      .create()
      .mapShapes(
        model,
        shape -> {
          if (shape.isStringShape() && shape.hasTrait(EnumTrait.class)) {
            return EnumShape.fromStringShape(shape.asStringShape().get()).get();
          } else {
            return shape;
          }
        }
      );
  }
}
