// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.wrappedlocalservice.extensions;

import software.amazon.polymorph.smithypython.common.nameresolver.SmithyNameResolver;
import software.amazon.polymorph.smithypython.common.nameresolver.Utils;
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

import java.util.Map;

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

  public DafnyPythonWrappedLocalServiceClientCodegenPlugin(Map<String, String> smithyNamespaceToPythonModuleNameMap) {
    super();
    SmithyNameResolver.setSmithyNamespaceToPythonModuleNameMap(smithyNamespaceToPythonModuleNameMap);
  }
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
      if (shape.equals(serviceShape)) {
        if (!shape.hasTrait(LocalServiceTrait.class)) {
          throw new IllegalArgumentException("ServiceShape for LocalService test MUST have a LocalServiceTrait: "
              + serviceShape);
        }
        return serviceShape.toBuilder()
            .addTrait(WrappedLocalServiceTrait.builder().build())
            .build();
      } else {
        return shape;
      }
    });
  }
}
