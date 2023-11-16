// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.localservice.extensions;

import software.amazon.polymorph.smithypython.wrappedlocalservice.WrappedLocalServiceTrait;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.traits.ReferenceTrait;
import software.amazon.smithy.build.PluginContext;
import software.amazon.smithy.build.SmithyBuildPlugin;
import software.amazon.smithy.codegen.core.directed.CodegenDirector;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.MemberShape;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.shapes.ShapeId;
import software.amazon.smithy.model.shapes.StructureShape;
import software.amazon.smithy.model.traits.ErrorTrait;
import software.amazon.smithy.model.traits.TraitDefinition;
import software.amazon.smithy.model.transform.ModelTransformer;
import software.amazon.smithy.python.codegen.DirectedPythonCodegen;
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
 */
@SmithyUnstableApi
public final class DafnyPythonLocalServiceClientCodegenPlugin implements SmithyBuildPlugin {

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
    Model transformedModel = transformServiceShapeToAddReferenceResources(context.getModel(), serviceShape);
    runner.model(transformedModel);

    runner.run();
  }

  public static Model transformServiceShapeToAddReferenceResources(Model model, ServiceShape serviceShape) {

    ServiceShape.Builder transformedServiceShapeBuilder = serviceShape.toBuilder();
    ModelTransformer.create().mapShapes(model, shape -> {
      if (shape.hasTrait(ReferenceTrait.class)) {

        ShapeId referenceShapeId = shape.expectTrait(ReferenceTrait.class).getReferentId();
        if (model.expectShape(referenceShapeId).isResourceShape()) {
          transformedServiceShapeBuilder.addResource(referenceShapeId);
        // TODO-Python: How to point codegen to reference services...
        } else if (model.expectShape(referenceShapeId).isServiceShape()) {
          // In theory: if there is another service shape, I shouldn't need to do anythign??
          // since it MUST be a dependency service,
          // which has a separate model and i can defer to its namespace...
//          transformedServiceShapeBuilder.add
//          transformedServiceShapeBuilder.
//          System.out.println("serviceshape adding as resource " + referenceShapeId);
//          transformedServiceShapeBuilder.addResource(referenceShapeId);
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