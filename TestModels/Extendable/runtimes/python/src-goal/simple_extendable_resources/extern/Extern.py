# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple.extendable.resources.internaldafny.wrapped
from simple_extendable_resources.smithy_generated.simple_extendable_resources.client import SimpleExtendableResources
from simple_extendable_resources.smithy_generated.simple_extendable_resources.shim import (
    SimpleExtendableResourcesShim,
)
from simple_extendable_resources.smithy_generated.simple_extendable_resources.config import (
    dafny_config_to_smithy_config
)
import Wrappers_Compile
from .NativeResource import  NativeResource
import ExtendableResource_Compile

@staticmethod
def WrappedSimpleExtendableResources(config):
    wrapped_config = dafny_config_to_smithy_config(config)
    impl = SimpleExtendableResources(wrapped_config)
    print("impl")
    print(impl)
    wrapped_client = SimpleExtendableResourcesShim(impl)
    return Wrappers_Compile.Result_Success(wrapped_client)

class NativeResourceFactory:

    @staticmethod
    def DafnyFactory():
        dafny_resource = ExtendableResource_Compile.ExtendableResource()
        dafny_resource.ctor__()
        native_resource = NativeResource(dafny_resource)

        # to_dafny
        return native_resource


simple.extendable.resources.internaldafny.wrapped.default__.WrappedSimpleExtendableResources = WrappedSimpleExtendableResources
simple.extendable.resources.internaldafny.nativeresourcefactory.default__ = NativeResourceFactory

DafnyFactory = NativeResourceFactory