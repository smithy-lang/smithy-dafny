# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from simple_refinement.smithygenerated.simple_refinement.client import SimpleRefinement
from simple_refinement.smithygenerated.simple_refinement.shim import SimpleRefinementShim
from simple_refinement.smithygenerated.simple_refinement.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleRefinementService

class default__(WrappedSimpleRefinementService.default__):

    @staticmethod
    def WrappedSimpleRefinement(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleRefinement(wrapped_config)
        wrapped_client = SimpleRefinementShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleRefinementService.default__ = default__