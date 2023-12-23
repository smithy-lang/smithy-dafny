# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# TODO-Python-PYTHONPATH: Qualify imports
import simple_refinement_internaldafny_wrapped
from smithygenerated.simple_refinement.client import SimpleRefinement
from smithygenerated.simple_refinement.shim import SimpleRefinementShim
from smithygenerated.simple_refinement.config import dafny_config_to_smithy_config
import Wrappers

class default__(simple_refinement_internaldafny_wrapped.default__):

    @staticmethod
    def WrappedSimpleRefinement(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleRefinement(wrapped_config)
        wrapped_client = SimpleRefinementShim(impl)
        return Wrappers.Result_Success(wrapped_client)

# (TODO-Python-PYTHONPATH: Remove)
simple_refinement_internaldafny_wrapped.default__ = default__
