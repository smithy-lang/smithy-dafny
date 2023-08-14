# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_refinement_internaldafny_wrapped
from simple_refinement.smithygenerated.client import SimpleRefinement
from simple_refinement.smithygenerated.shim import SimpleRefinementShim
import Wrappers

@staticmethod
def WrappedSimpleRefinement(config):
    wrapped_config = config
    impl = SimpleRefinement(wrapped_config)
    wrapped_client = SimpleRefinementShim(impl)
    return Wrappers.Result_Success(wrapped_client)

simple_refinement_internaldafny_wrapped.default__.WrappedSimpleRefinement = WrappedSimpleRefinement
