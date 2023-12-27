# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import ExtendableResource
from simple_extendable_resources.smithygenerated.simple_extendable_resources.references import IExtendableResource

class default__(IExtendableResource):
  # Importing the type at top-level results in circular dependency import issue
  from simple_extendable_resources_internaldafny_types import IExtendableResource as DafnyIExtendableResource
  _impl: DafnyIExtendableResource

  def __init__(self, _impl):
    self._impl = _impl

  def GetExtendableResourceData(self, nativeInput):
    return self._impl.GetExtendableResourceData(nativeInput)

  def AlwaysModeledError(self, nativeInput):
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
    native_resource = default__(dafny_resource)
    return native_resource


# TODO-Python-PYTHONPATH: Remove import and try/catch, only needed for path issues
# Problem: simple_extendable_resources_internaldafny_nativeresourcefactory is only built in tests,
#   but SimpleDependencies relies on this current file,
#   and ExtendableResource's tests are not built for another file's src.
# Workaround: Only import if able.
# Fix: Remove PYTHONPATH workaround.
try:
  import simple_extendable_resources_internaldafny_nativeresourcefactory
  simple_extendable_resources_internaldafny_nativeresourcefactory.default__ = NativeResourceFactory
except ModuleNotFoundError:
  pass
