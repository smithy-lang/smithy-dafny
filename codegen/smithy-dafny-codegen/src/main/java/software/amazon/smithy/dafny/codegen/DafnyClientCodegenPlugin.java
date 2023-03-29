// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.smithy.dafny.codegen;

import software.amazon.smithy.build.PluginContext;
import software.amazon.smithy.build.SmithyBuildPlugin;

public final class DafnyClientCodegenPlugin implements SmithyBuildPlugin {
    @Override
    public String getName() {
        return "dafny-client-codegen";
    }

    @Override
    public void execute(PluginContext context) {
        // TODO: move this into a DirectedCodegen.customizeBeforeShapeGeneration implementation
        // Model model = ModelUtils.addMissingErrorMessageMembers(context.getModel());

        // TODO generate code
    }
}
