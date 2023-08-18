# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

from simple_extendable_resources_internaldafny_types import (
  IExtendableResource as DafnyIExtendableResource
)
import ExtendableResource
from simple_extendable_resources.smithygenerated.models import IExtendableResource
import simple_extendable_resources_internaldafny_nativeresourcefactory

class NativeResource(IExtendableResource):
  _impl: DafnyIExtendableResource

  def __init__(self, _impl):
    self._impl = _impl

  def GetExtendableResourceData(self, nativeInput):
    print("nativeInput")
    print(nativeInput)
    a = self._impl.GetExtendableResourceData(nativeInput)
    print("a")
    print(a)
    return a

  def AlwaysModeledError(self, nativeInput):
    print("AlwaysModeledError")
    print(nativeInput)
    return self._impl.AlwaysModeledError(nativeInput)

  def AlwaysMultipleErrors(self, nativeInput):
    return self._impl.AlwaysMultipleErrors(nativeInput)

  def AlwaysOpaqueError(self, nativeInput):
    if nativeInput.value == None:
      raise Exception("Python Hard Coded Exception")
    return self._impl.AlwaysOpaqueError(nativeInput)

class NativeResourceFactory:

  @staticmethod
  def DafnyFactory():
    dafny_resource = ExtendableResource.ExtendableResource()
    dafny_resource.ctor__()
    native_resource = NativeResource(dafny_resource)

    # to_dafny
    return native_resource


simple_extendable_resources_internaldafny_nativeresourcefactory.default__ = NativeResourceFactory

DafnyFactory = NativeResourceFactory