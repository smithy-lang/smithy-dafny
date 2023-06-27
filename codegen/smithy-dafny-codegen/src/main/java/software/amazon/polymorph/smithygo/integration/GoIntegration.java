// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithygo.integration;

import software.amazon.polymorph.smithygo.GoCodegenContext;
import software.amazon.polymorph.smithygo.GoSettings;
import software.amazon.polymorph.smithygo.GoWriter;
import software.amazon.smithy.codegen.core.SmithyIntegration;

public interface GoIntegration extends SmithyIntegration<GoSettings, GoWriter, GoCodegenContext> {
}
