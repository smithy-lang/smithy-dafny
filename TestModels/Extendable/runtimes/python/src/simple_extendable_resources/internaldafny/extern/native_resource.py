# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

import simple_extendable_resources.internaldafny.generated.ExtendableResource as ExtendableResource
from simple_extendable_resources.smithygenerated.simple_extendable_resources.references import IExtendableResource
from simple_extendable_resources.internaldafny.generated.SimpleExtendableResourcesTypes import IExtendableResource as DafnyIExtendableResource

class default__(IExtendableResource):

  _impl: DafnyIExtendableResource

  def __init__(self, _impl):
    self._impl = _impl

  def get_extendable_resource_data(self, nativeInput):
    return self._impl.GetExtendableResourceData(nativeInput)

  def always_modeled_error(self, nativeInput):
    return self._impl.AlwaysModeledError(nativeInput)

  def always_multiple_errors(self, nativeInput):
    return self._impl.AlwaysMultipleErrors(nativeInput)

  def always_opaque_error(self, nativeInput):
    if nativeInput.value == None:
      raise Exception("Python Hard Coded Exception")
    return self._impl.AlwaysOpaqueError(nativeInput)

class my_NativeResourceFactory:

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
  import NativeResourceFactory
  NativeResourceFactory.default__ = my_NativeResourceFactory
except ModuleNotFoundError:
  pass
