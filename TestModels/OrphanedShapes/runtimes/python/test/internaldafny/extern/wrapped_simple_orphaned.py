# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# src imports
from simple_orphaned.smithygenerated.simple_orphaned.client import SimpleOrphaned
from simple_orphaned.smithygenerated.simple_orphaned.shim import SimpleOrphanedShim
from simple_orphaned.smithygenerated.simple_orphaned.config import dafny_config_to_smithy_config
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

# test imports, not qualified since this isn't in a package
import WrappedSimpleOrphanedService

class default__(WrappedSimpleOrphanedService.default__):

    @staticmethod
    def WrappedSimpleOrphaned(config):
        wrapped_config = dafny_config_to_smithy_config(config)
        impl = SimpleOrphaned(wrapped_config)
        wrapped_client = SimpleOrphanedShim(impl)
        return Wrappers.Result_Success(wrapped_client)

WrappedSimpleOrphanedService.default__ = default__