// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithypython.awssdk.extensions;

import software.amazon.polymorph.smithypython.awssdk.DafnyAwsSdkProtocolTrait;
import software.amazon.polymorph.smithypython.wrappedlocalservice.WrappedLocalServiceTrait;
import software.amazon.polymorph.traits.LocalServiceTrait;
import software.amazon.smithy.build.PluginContext;
import software.amazon.smithy.build.SmithyBuildPlugin;
import software.amazon.smithy.codegen.core.directed.CodegenDirector;
import software.amazon.smithy.model.Model;
import software.amazon.smithy.model.shapes.ServiceShape;
import software.amazon.smithy.model.transform.ModelTransformer;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonSettings;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.integration.PythonIntegration;
import software.amazon.smithy.utils.SmithyUnstableApi;

/**
 * Plugin to trigger Smithy-Dafny Python code generation for AWS SDK services.
 * This Plugin differs from the PythonClientCodegenPlugin by not calling
 *     runner.performDefaultCodegenTransforms();
 * and
 *     runner.createDedicatedInputsAndOutputs();
 * These methods transform the model in ways that the model does not align with
 *   the generated Dafny code.
 * This Plugin also attaches a DafnyAwsSdkProtocolTrait to the ServiceShape provided in settings.
 * AWS SDKs do not consistently label a protocol,
 */
@SmithyUnstableApi
public final class DafnyPythonAwsSdkClientCodegenPlugin implements SmithyBuildPlugin {
  @Override
  public String getName() {
    return "dafny-python-aws-sdk-client-codegen";
  }

  @Override
  public void execute(PluginContext context) {
    CodegenDirector<PythonWriter, PythonIntegration, GenerationContext, PythonSettings> runner
        = new CodegenDirector<>();

    PythonSettings settings = PythonSettings.from(context.getSettings());
    settings.setProtocol(DafnyAwsSdkProtocolTrait.ID);
    runner.settings(settings);
    runner.directedCodegen(new DirectedDafnyPythonAwsSdkCodegen());
    runner.fileManifest(context.getFileManifest());
    runner.service(settings.getService());
    runner.model(context.getModel());
    runner.integrationClass(PythonIntegration.class);

    // Add a DafnyAwsSdkProtocolTrait to the service as a contextual indicator highlighting
    //   that the DafnyPythonAwsSdk protocol should be used.
    ServiceShape serviceShape = context.getModel().expectShape(settings.getService()).asServiceShape().get();
    runner.model(addAwsSdkProtocolTrait(context.getModel(), serviceShape));

    runner.run();
  }

  public static Model addAwsSdkProtocolTrait(Model model, ServiceShape serviceShape) {
    return ModelTransformer.create().mapShapes(model, shape -> {
      if (shape instanceof ServiceShape && shape.hasTrait(LocalServiceTrait.class)) {
        return serviceShape.toBuilder()
            .addTrait(DafnyAwsSdkProtocolTrait.builder().build())
            .build();
      } else {
        return shape;
      }
    });
  }
}
