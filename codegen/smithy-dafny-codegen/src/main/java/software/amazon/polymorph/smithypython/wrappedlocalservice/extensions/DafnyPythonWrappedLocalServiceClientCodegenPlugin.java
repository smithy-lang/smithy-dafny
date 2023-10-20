
/*
 * Copyright Amazon.com, Inc. or its affiliates. All Rights Reserved.
 *
 * Licensed under the Apache License, Version 2.0 (the "License").
 * You may not use this file except in compliance with the License.
 * A copy of the License is located at
 *
 *  http://aws.amazon.com/apache2.0
 *
 * or in the "license" file accompanying this file. This file is distributed
 * on an "AS IS" BASIS, WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either
 * express or implied. See the License for the specific language governing
 * permissions and limitations under the License.
 */

package software.amazon.polymorph.smithypython.wrappedlocalservice.extensions;

import software.amazon.polymorph.smithypython.wrappedlocalservice.extensions.DirectedDafnyPythonWrappedLocalServiceCodegen;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.polymorph.smithypython.wrappedlocalservice.WrappedLocalServiceTrait;
import software.amazon.smithy.build.PluginContext;
import software.amazon.smithy.build.SmithyBuildPlugin;
import software.amazon.smithy.codegen.core.directed.CodegenDirector;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.transform.ModelTransformer;
import software.amazon.smithy.python.codegen.DirectedPythonCodegen;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonSettings;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.integration.PythonIntegration;
import software.amazon.smithy.utils.SmithyUnstableApi;

/**
 * Plugin to trigger Smithy-Dafny Python code generation for a wrapped localService.
 * This differs from the PythonClientCodegenPlugin by not calling
 *     runner.performDefaultCodegenTransforms();
 * and
 *     runner.createDedicatedInputsAndOutputs();
 * This differs from the non-wrapped plugin by adding a WrappedLocalServiceTrait
 *   to the service that is being generated. This is stores the context that this plugin
 *   requires wrapped localService generation, so that we can identify this from within
 *   code generation.
 * These methods transform the model such that the model used by the code generator does not align with
 *   the generated Dafny code.
 */
@SmithyUnstableApi
public final class DafnyPythonWrappedLocalServiceClientCodegenPlugin implements SmithyBuildPlugin {

  @Override
  public String getName() {
    return "dafny-python-wrapped-local-service-client-codegen";
  }

  @Override
  public void execute(PluginContext context) {
    CodegenDirector<PythonWriter, PythonIntegration, GenerationContext, PythonSettings> runner
        = new CodegenDirector<>();

    PythonSettings settings = PythonSettings.from(context.getSettings());
    settings.setProtocol(WrappedLocalServiceTrait.ID);
    runner.settings(settings);
    runner.directedCodegen(new DirectedDafnyPythonWrappedLocalServiceCodegen());
    runner.fileManifest(context.getFileManifest());
    runner.service(settings.getService());
    runner.integrationClass(PythonIntegration.class);

    // Add a WrappedLocalServiceTrait to the serviceShape to indicate to codegen
    //   that this shape requires
    ServiceShape serviceShape = context.getModel().expectShape(settings.getService()).asServiceShape().get();
    Model transformedModel = addWrappedLocalServiceTrait(context.getModel(), serviceShape);
    runner.model(transformedModel);

    runner.run();
  }

  public static Model addWrappedLocalServiceTrait(Model model, ServiceShape serviceShape) {
    return ModelTransformer.create().mapShapes(model, shape -> {
      if (shape instanceof ServiceShape && shape.hasTrait(LocalServiceTrait.class)) {
        return serviceShape.toBuilder()
            .addTrait(WrappedLocalServiceTrait.builder().build())
            .build();
      } else {
        return shape;
      }
    });
  }
}
