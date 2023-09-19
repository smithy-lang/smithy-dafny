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

package software.amazon.polymorph.smithypython.extensions;

import software.amazon.polymorph.smithypython.Constants.GenerationType;
import software.amazon.smithy.build.PluginContext;
import software.amazon.smithy.build.SmithyBuildPlugin;
import software.amazon.smithy.codegen.core.directed.CodegenDirector;
import software.amazon.smithy.python.codegen.DirectedPythonCodegen;
import software.amazon.smithy.python.codegen.GenerationContext;
import software.amazon.smithy.python.codegen.PythonSettings;
import software.amazon.smithy.python.codegen.PythonWriter;
import software.amazon.smithy.python.codegen.integration.PythonIntegration;
import software.amazon.smithy.utils.SmithyUnstableApi;

/**
 * Plugin to trigger Python code generation.
 */
@SmithyUnstableApi
public final class DafnyPythonClientCodegenPlugin implements SmithyBuildPlugin {
  private boolean shouldPerformDefaultCodegenTransforms = true;
  private boolean shouldCreateDedicatedInputsAndOutputs = true;
  private GenerationType generationType;

  @Override
  public String getName() {
    return "dafny-python-client-codegen";
  }

  public void disablePerformDefaultCodegenTransforms() {
    shouldPerformDefaultCodegenTransforms = false;
  }

  public void disableCreateDedicatedInputsAndOutputs() {
    shouldCreateDedicatedInputsAndOutputs = false;
  }

  public void setGenerationType(GenerationType generationType) {
    this.generationType = generationType;
  }

  @Override
  public void execute(PluginContext context) {
    CodegenDirector<PythonWriter, PythonIntegration, GenerationContext, PythonSettings> runner
        = new CodegenDirector<>();

    DafnyPythonSettings settings = DafnyPythonSettings.from(context.getSettings());
    settings.setGenerationType(this.generationType);
    runner.settings(settings);
    runner.directedCodegen(new DirectedPythonCodegen());
    runner.fileManifest(context.getFileManifest());
    runner.service(settings.getService());
    runner.model(context.getModel());
    runner.integrationClass(PythonIntegration.class);
    if (shouldPerformDefaultCodegenTransforms) {
      runner.performDefaultCodegenTransforms();
    }
    if (shouldCreateDedicatedInputsAndOutputs) {
      runner.createDedicatedInputsAndOutputs();
    }
    runner.run();
  }
}
