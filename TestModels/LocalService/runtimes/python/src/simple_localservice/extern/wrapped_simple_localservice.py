# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_localservice_internaldafny_wrapped
from simple_localservice.smithygenerated.client import SimpleLocalService
from simple_localservice.smithygenerated.config import dafny_config_to_smithy_config
from simple_localservice.smithygenerated.shim import SimpleLocalServiceShim
import Wrappers

@staticmethod
def WrappedSimpleLocalService(config):
    wrapped_config = dafny_config_to_smithy_config(config)
    impl = SimpleLocalService(wrapped_config)
    wrapped_client = SimpleLocalServiceShim(impl)
    return Wrappers.Result_Success(wrapped_client)

simple_localservice_internaldafny_wrapped.default__.WrappedSimpleLocalService = WrappedSimpleLocalService
