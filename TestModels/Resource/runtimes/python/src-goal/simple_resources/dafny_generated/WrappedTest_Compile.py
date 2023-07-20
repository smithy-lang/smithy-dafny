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
import simple.resources.internaldafny.types
import Helpers_Compile
import SimpleResource_Compile
import SimpleResourcesOperations_Compile
import simple.resources.internaldafny.impl
import SimpleResourcesTest_Compile
import simple.resources.internaldafny.wrapped

assert "WrappedTest_Compile" == __name__
WrappedTest_Compile = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "WrappedTest_Compile._default"
    @staticmethod
    def TestWrappedClient(config):
        d_89_client_: simple.resources.internaldafny.types.ISimpleResourcesClient
        d_90_valueOrError0_: Wrappers_Compile.Result = None
        out8_: Wrappers_Compile.Result
        out8_ = simple.resources.internaldafny.wrapped.default__.WrappedSimpleResources(config)
        d_90_valueOrError0_ = out8_
        if not(not((d_90_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Resource/test/WrappedTest.dfy(15,15): " + _dafny.string_of(d_90_valueOrError0_))
        d_89_client_ = (d_90_valueOrError0_).Extract()
        d_91_resource_: simple.resources.internaldafny.types.ISimpleResource
        out9_: simple.resources.internaldafny.types.ISimpleResource
        out9_ = SimpleResourcesTest_Compile.default__.TestGetResources(config, d_89_client_)
        d_91_resource_ = out9_
        SimpleResourcesTest_Compile.default__.TestNoneGetData(config, d_91_resource_)
        SimpleResourcesTest_Compile.default__.TestSomeGetData(config, d_91_resource_)

    @staticmethod
    def WrappedTestDefaultConfig():
        WrappedTest_Compile.default__.TestWrappedClient(simple.resources.internaldafny.wrapped.default__.WrappedDefaultSimpleResourcesConfig())

    @staticmethod
    def WrappedTestCustomConfig():
        WrappedTest_Compile.default__.TestWrappedClient(simple.resources.internaldafny.types.SimpleResourcesConfig_SimpleResourcesConfig(_dafny.Seq("Dafny")))

