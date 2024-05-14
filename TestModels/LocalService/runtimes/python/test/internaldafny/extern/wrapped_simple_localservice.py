# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# TODO-Python-PYTHONPATH: Qualify imports
import simple_localservice_internaldafny_wrapped
from simple_localservice.smithygenerated.simple_localservice.client import SimpleLocalService
from simple_localservice.smithygenerated.simple_localservice.shim import SimpleLocalServiceShim
from simple_localservice.smithygenerated.simple_localservice.config import dafny_config_to_smithy_config
import standard_library.internaldafny.generated.Wrappers as Wrappers

class default__(simple_localservice_internaldafny_wrapped.default__):

    @staticmethod
    def WrappedSimpleLocalService(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleLocalService(wrapped_config)
        wrapped_client = SimpleLocalServiceShim(impl)
        return Wrappers.Result_Success(wrapped_client)

# (TODO-Python-PYTHONPATH: Remove)
simple_localservice_internaldafny_wrapped.default__ = default__
