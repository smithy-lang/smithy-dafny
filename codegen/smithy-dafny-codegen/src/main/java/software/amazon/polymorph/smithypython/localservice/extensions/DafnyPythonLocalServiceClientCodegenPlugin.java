// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice.extensions;

import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.traits.JavaDocTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.build.PluginContext;
import software.amazon.smithy.build.SmithyBuildPlugin;
import software.amazon.smithy.codegen.core.directed.CodegenDirector;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.AbstractShapeBuilder;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.traits.DocumentationTrait;
import software.amazon.smithy.model.transform.ModelTransformer;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonSettings;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.integration.PythonIntegration;
import software.amazon.smithy.utils.SmithyUnstableApi;

import java.util.Map;

/**
 * Plugin to trigger Smithy-Dafny Python code generation.
 * This differs from the PythonClientCodegenPlugin by not calling
 *     runner.performDefaultCodegenTransforms();
 * and
 *     runner.createDedicatedInputsAndOutputs();
 * These methods transform the model in ways that the model does not align with
 *   the generated Dafny code.
 * This also transforms the model to bridge the gap between Polymorph-flavored Smithy and standard Smithy.
 */
@SmithyUnstableApi
public final class DafnyPythonLocalServiceClientCodegenPlugin implements SmithyBuildPlugin {

  public DafnyPythonLocalServiceClientCodegenPlugin(Map<String, String> smithyNamespaceToPythonModuleNameMap) {
    super();
    SmithyNameResolver.setSmithyNamespaceToPythonModuleNameMap(smithyNamespaceToPythonModuleNameMap);
  }

  @Override
  public String getName() {
    return "dafny-python-localservice-client-codegen";
  }

  @Override
  public void execute(PluginContext context) {
    CodegenDirector<PythonWriter, PythonIntegration, GenerationContext, PythonSettings> runner
        = new CodegenDirector<>();

    PythonSettings settings = PythonSettings.from(context.getSettings());
    runner.settings(settings);
    runner.directedCodegen(new DirectedDafnyPythonLocalServiceCodegen());
    runner.fileManifest(context.getFileManifest());
    runner.service(settings.getService());
    runner.model(context.getModel());
    runner.integrationClass(PythonIntegration.class);

    ServiceShape serviceShape = context.getModel().expectShape(settings.getService()).asServiceShape().get();
    Model transformedModel = transformModelForLocalService(context.getModel(), serviceShape);
    runner.model(transformedModel);

    runner.run();
  }

  public static Model transformModelForLocalService(Model model, ServiceShape serviceShape) {
    Model transformedModel = model;
    transformedModel = transformJavadocTraitsToDocumentationTraits(transformedModel);
    transformedModel = transformServiceShapeToAddReferenceResources(transformedModel, serviceShape);
    return transformedModel;
  }

  /**
   * For each object with a Polymorph {@link JavaDocTrait} containing documentation,
   * add a new Smithy {@link DocumentationTrait} with that documentation.
   * Smithy-Python will generate pydocs for DocumentationTraits.
   * @param model
   * @return
   */
  public static Model transformJavadocTraitsToDocumentationTraits(Model model) {
    return ModelTransformer.create().mapShapes(model, shape -> {
      if (shape.hasTrait(JavaDocTrait.class)) {
        JavaDocTrait javaDocTrait = shape.getTrait(JavaDocTrait.class).get();
        DocumentationTrait documentationTrait = new DocumentationTrait(javaDocTrait.getValue());

        // This is painful, but there is nothing like `shape.getUnderlyingShapeType`...
        // instead, check every possible shape for its builder...
        AbstractShapeBuilder<?,?> builder;
        if (shape.isBlobShape()) {
          builder = shape.asBlobShape().get().toBuilder();
        } else if (shape.isBooleanShape()) {
          builder = shape.asBooleanShape().get().toBuilder();
        } else if (shape.isDocumentShape()) {
          builder = shape.asDocumentShape().get().toBuilder();
        } else if (shape.isStringShape()) {
          builder = shape.asStringShape().get().toBuilder();
        } else if (shape.isTimestampShape()) {
          builder = shape.asTimestampShape().get().toBuilder();
        } else if (shape.isByteShape()) {
          builder = shape.asByteShape().get().toBuilder();
        } else if (shape.isIntegerShape()) {
          builder = shape.asIntegerShape().get().toBuilder();
        } else if (shape.isFloatShape()) {
          builder = shape.asFloatShape().get().toBuilder();
        } else if (shape.isBigIntegerShape()) {
          builder = shape.asBigIntegerShape().get().toBuilder();
        } else if (shape.isShortShape()) {
          builder = shape.asShortShape().get().toBuilder();
        } else if (shape.isLongShape()) {
          builder = shape.asLongShape().get().toBuilder();
        } else if (shape.isDoubleShape()) {
          builder = shape.asDoubleShape().get().toBuilder();
        } else if (shape.isBigDecimalShape()) {
          builder = shape.asBigDecimalShape().get().toBuilder();
        } else if (shape.isListShape()) {
          builder = shape.asListShape().get().toBuilder();
        } else if (shape.isSetShape()) {
          builder = shape.asSetShape().get().toBuilder();
        } else if (shape.isMapShape()) {
          builder = shape.asMapShape().get().toBuilder();
        } else if (shape.isStructureShape()) {
          builder = shape.asStructureShape().get().toBuilder();
        } else if (shape.isUnionShape()) {
          builder = shape.asUnionShape().get().toBuilder();
        } else if (shape.isServiceShape()) {
          builder = shape.asServiceShape().get().toBuilder();
        } else if (shape.isOperationShape()) {
          builder = shape.asOperationShape().get().toBuilder();
        } else if (shape.isResourceShape()) {
          builder = shape.asResourceShape().get().toBuilder();
        } else if (shape.isMemberShape()) {
          builder = shape.asMemberShape().get().toBuilder();
        } else if (shape.isEnumShape()) {
          builder = shape.asEnumShape().get().toBuilder();
        } else if (shape.isIntEnumShape()) {
          builder = shape.asIntEnumShape().get().toBuilder();
        } else {
          // Unfortunately, there is no "default" shape...
          // The above should cover all shapes; if not, new shapes need to be added above.
          throw new IllegalArgumentException("Unable to process @javadoc trait on unsupported shape type: " + shape);
        }
        builder.addTrait(documentationTrait);
        return builder.build();
      } else {
        return shape;
      }
    });
  }

  /**
   * Smithy-Python requires that resource shapes are attached to a ServiceShape.
   * Smithy-Python also does not understand Polymorph's {@link ReferenceTrait}.
   * This parses Polymorph's ReferenceTrait to attach any referenced resources to the {@param serviceShape}.
   * @param model
   * @param serviceShape
   * @return
   */
  public static Model transformServiceShapeToAddReferenceResources(Model model, ServiceShape serviceShape) {

    ServiceShape.Builder transformedServiceShapeBuilder = serviceShape.toBuilder();
    ModelTransformer.create().mapShapes(model, shape -> {
      if (shape.hasTrait(ReferenceTrait.class)) {

        ShapeId referenceShapeId = shape.expectTrait(ReferenceTrait.class).getReferentId();
        if (model.expectShape(referenceShapeId).isResourceShape()) {
          transformedServiceShapeBuilder.addResource(referenceShapeId);
        }
      }
      return shape;
    });

    return ModelTransformer.create().mapShapes(model, shape -> {
      if (shape.equals(serviceShape)) {
        return transformedServiceShapeBuilder.build();
      } else {
        return shape;
      }
    });
  }
}