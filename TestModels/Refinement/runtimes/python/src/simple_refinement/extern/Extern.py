# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple.refinement.internaldafny.wrapped
from simple_refinement.smithy_generated.simple_refinement.client import SimpleRefinement
from simple_refinement.smithy_generated.simple_refinement.shim import SimpleRefinementShim
import Wrappers_Compile

@staticmethod
def WrappedSimpleRefinement(config):
    wrapped_config = config
    impl = SimpleRefinement(wrapped_config)
    wrapped_client = SimpleRefinementShim(impl)
    return Wrappers_Compile.Result_Success(wrapped_client)

simple.refinement.internaldafny.wrapped.default__.WrappedSimpleRefinement = WrappedSimpleRefinement
