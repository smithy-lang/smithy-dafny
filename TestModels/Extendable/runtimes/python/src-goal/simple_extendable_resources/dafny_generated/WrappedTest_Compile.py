import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import Wrappers_Compile
import StandardLibrary_mUInt_Compile
import StandardLibrary_Compile
import UTF8
import simple.extendable.resources.internaldafny.types
import ExtendableResource_Compile
import TestHelpers_Compile
import SimpleExtendableResourcesOperations_Compile
import simple.extendable.resources.internaldafny.impl
import simple.extendable.resources.internaldafny.nativeresourcefactory
import SimpleExtendableResourcesTest_Compile
import simple.extendable.resources.internaldafny.wrapped
import NativeExtendableResourceTest_Compile

assert "WrappedTest_Compile" == __name__
WrappedTest_Compile = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "WrappedTest_Compile._default"
    @staticmethod
    def WrappedTestClientDafnyResource():
        d_141_client_: simple.extendable.resources.internaldafny.types.ISimpleExtendableResourcesClient
        d_142_valueOrError0_: Wrappers_Compile.Result = None
        out35_: Wrappers_Compile.Result
        out35_ = simple.extendable.resources.internaldafny.wrapped.default__.WrappedSimpleExtendableResources(simple.extendable.resources.internaldafny.wrapped.default__.WrappedDefaultSimpleExtendableResourcesConfig())
        d_142_valueOrError0_ = out35_
        if not(not((d_142_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/WrappedTest.dfy(23,15): " + _dafny.string_of(d_142_valueOrError0_))
        d_141_client_ = (d_142_valueOrError0_).Extract()
        d_143_resource_: simple.extendable.resources.internaldafny.types.IExtendableResource
        out36_: simple.extendable.resources.internaldafny.types.IExtendableResource
        out36_ = SimpleExtendableResourcesTest_Compile.default__.TestCreateExtendableResource(d_141_client_, (SimpleExtendableResourcesTest_Compile.default__).TEST__RESOURCE__NAME)
        d_143_resource_ = out36_
        SimpleExtendableResourcesTest_Compile.default__.TestNoneUseExtendableResource(d_141_client_, d_143_resource_, (SimpleExtendableResourcesTest_Compile.default__).TEST__RESOURCE__NAME)
        SimpleExtendableResourcesTest_Compile.default__.TestSomeUseExtendableResource(d_141_client_, d_143_resource_, (SimpleExtendableResourcesTest_Compile.default__).TEST__RESOURCE__NAME)
        SimpleExtendableResourcesTest_Compile.default__.TestUseAlwaysModeledError(d_141_client_, d_143_resource_)
        SimpleExtendableResourcesTest_Compile.default__.TestUseAlwaysMultipleErrors(d_141_client_, d_143_resource_)
        SimpleExtendableResourcesTest_Compile.default__.TestUseAlwaysOpaqueError(d_141_client_, d_143_resource_)

    @staticmethod
    def WrappedTestClientNativeResource():
        d_144_client_: simple.extendable.resources.internaldafny.types.ISimpleExtendableResourcesClient
        d_145_valueOrError0_: Wrappers_Compile.Result = None
        out37_: Wrappers_Compile.Result
        out37_ = simple.extendable.resources.internaldafny.wrapped.default__.WrappedSimpleExtendableResources(simple.extendable.resources.internaldafny.wrapped.default__.WrappedDefaultSimpleExtendableResourcesConfig())
        d_145_valueOrError0_ = out37_
        if not(not((d_145_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/WrappedTest.dfy(36,15): " + _dafny.string_of(d_145_valueOrError0_))
        d_144_client_ = (d_145_valueOrError0_).Extract()
        d_146_resource_: simple.extendable.resources.internaldafny.types.IExtendableResource
        out38_: simple.extendable.resources.internaldafny.types.IExtendableResource
        out38_ = simple.extendable.resources.internaldafny.nativeresourcefactory.default__.DafnyFactory()
        d_146_resource_ = out38_
        SimpleExtendableResourcesTest_Compile.default__.TestNoneUseExtendableResource(d_144_client_, d_146_resource_, (ExtendableResource_Compile.default__).DEFAULT__RESOURCE__NAME)
        SimpleExtendableResourcesTest_Compile.default__.TestSomeUseExtendableResource(d_144_client_, d_146_resource_, (ExtendableResource_Compile.default__).DEFAULT__RESOURCE__NAME)
        SimpleExtendableResourcesTest_Compile.default__.TestUseAlwaysModeledError(d_144_client_, d_146_resource_)
        SimpleExtendableResourcesTest_Compile.default__.TestUseAlwaysMultipleErrors(d_144_client_, d_146_resource_)
        SimpleExtendableResourcesTest_Compile.default__.TestUseAlwaysOpaqueError(d_144_client_, d_146_resource_)

