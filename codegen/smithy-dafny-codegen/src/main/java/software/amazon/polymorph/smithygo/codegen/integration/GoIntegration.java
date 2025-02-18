// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0

package software.amazon.polymorph.smithygo.codegen.integration;

import software.amazon.polymorph.smithygo.codegen.GenerationContext;
import software.amazon.polymorph.smithygo.codegen.GoSettings;
import software.amazon.polymorph.smithygo.codegen.GoWriter;
import software.amazon.smithy.codegen.core.SmithyIntegration;

public interface GoIntegration
  extends SmithyIntegration<GoSettings, GoWriter, GenerationContext> {}
