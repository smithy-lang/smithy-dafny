# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# TODO-Python-PYTHONPATH: Qualify imports
import simple_types_smithystring_internaldafny_wrapped
from simple_types_smithystring.smithygenerated.simple_types_smithystring.client import SimpleTypesString
from simple_types_smithystring.smithygenerated.simple_types_smithystring.shim import SimpleStringShim
from simple_types_smithystring.smithygenerated.simple_types_smithystring.config import dafny_config_to_smithy_config
import Wrappers

class default__(simple_types_smithystring_internaldafny_wrapped.default__):

    @staticmethod
    def WrappedSimpleString(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleTypesString(wrapped_config)
        wrapped_client = SimpleStringShim(impl)
        return Wrappers.Result_Success(wrapped_client)

# (TODO-Python-PYTHONPATH: Remove)
simple_types_smithystring_internaldafny_wrapped.default__ = default__
