# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# TODO-Python-PYTHONPATH: Qualify imports
import simple_types_smithydouble_internaldafny_wrapped
from simple_types_smithydouble.smithygenerated.simple_types_smithydouble.client import SimpleTypesDouble
from simple_types_smithydouble.smithygenerated.simple_types_smithydouble.shim import SimpleDoubleShim
from simple_types_smithydouble.smithygenerated.simple_types_smithydouble.config import dafny_config_to_smithy_config
import Wrappers

class default__(simple_types_smithydouble_internaldafny_wrapped.default__):

    @staticmethod
    def WrappedSimpleDouble(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleTypesDouble(wrapped_config)
        wrapped_client = SimpleDoubleShim(impl)
        return Wrappers.Result_Success(wrapped_client)

# (TODO-Python-PYTHONPATH: Remove)
simple_types_smithydouble_internaldafny_wrapped.default__ = default__
