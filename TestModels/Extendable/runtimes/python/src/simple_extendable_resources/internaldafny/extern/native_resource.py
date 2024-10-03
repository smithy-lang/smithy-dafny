# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_extendable_resources.internaldafny.generated.ExtendableResource as ExtendableResource
from simple_extendable_resources.smithygenerated.simple_extendable_resources.references import IExtendableResource
import simple_extendable_resources.smithygenerated.simple_extendable_resources.dafny_to_smithy as dafny_to_smithy

class default__(IExtendableResource):

  _underlying_native_impl: IExtendableResource

  def __init__(self, _impl):
    self._underlying_native_impl = _impl

  def get_extendable_resource_data(self, nativeInput):
    return self._underlying_native_impl.get_extendable_resource_data(nativeInput)

  def always_modeled_error(self, nativeInput):
    return self._underlying_native_impl.always_modeled_error(nativeInput)

  def always_multiple_errors(self, nativeInput):
    return self._underlying_native_impl.always_multiple_errors(nativeInput)

  def always_opaque_error(self, nativeInput):
    if nativeInput.value == None:
      raise Exception("Python Hard Coded Exception")
    return self._underlying_native_impl.always_opaque_error(nativeInput)

class my_NativeResourceFactory:

  @staticmethod
  def DafnyFactory():
    dafny_resource = ExtendableResource.ExtendableResource()
    dafny_resource.ctor__()
    native_underlying_resource = dafny_to_smithy.simple_extendable_resources_ExtendableResourceReference(dafny_resource)
    native_resource = default__(native_underlying_resource)
    return native_resource
