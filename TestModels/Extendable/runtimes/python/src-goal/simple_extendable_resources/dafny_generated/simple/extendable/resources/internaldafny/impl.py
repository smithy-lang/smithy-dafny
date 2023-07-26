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

assert "simple.extendable.resources.internaldafny.impl" == __name__

class SimpleExtendableResourcesClient(simple.extendable.resources.internaldafny.types.ISimpleExtendableResourcesClient):
    def  __init__(self):
        self._config: SimpleExtendableResourcesOperations_Compile.Config = SimpleExtendableResourcesOperations_Compile.Config_Config.default()()
        pass

    def __dafnystr__(self) -> str:
        return "simple.extendable.resources.internaldafny.impl_Compile.SimpleExtendableResourcesClient"
    def ctor__(self, config):
        (self)._config = config

    def CreateExtendableResource(self, input):
        output: Wrappers_Compile.Result = None
        out12_: Wrappers_Compile.Result
        out12_ = SimpleExtendableResourcesOperations_Compile.default__.CreateExtendableResource((self).config, input)
        output = out12_
        return output

    def UseExtendableResource(self, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.extendable.resources.internaldafny.types.UseExtendableResourceOutput.default())()
        out13_: Wrappers_Compile.Result
        out13_ = SimpleExtendableResourcesOperations_Compile.default__.UseExtendableResource((self).config, input)
        output = out13_
        return output

    def UseExtendableResourceAlwaysModeledError(self, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsOutput.default())()
        out14_: Wrappers_Compile.Result
        out14_ = SimpleExtendableResourcesOperations_Compile.default__.UseExtendableResourceAlwaysModeledError((self).config, input)
        output = out14_
        return output

    def UseExtendableResourceAlwaysMultipleErrors(self, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsOutput.default())()
        out15_: Wrappers_Compile.Result
        out15_ = SimpleExtendableResourcesOperations_Compile.default__.UseExtendableResourceAlwaysMultipleErrors((self).config, input)
        output = out15_
        return output

    def UseExtendableResourceAlwaysOpaqueError(self, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsOutput.default())()
        out16_: Wrappers_Compile.Result
        out16_ = SimpleExtendableResourcesOperations_Compile.default__.UseExtendableResourceAlwaysOpaqueError((self).config, input)
        output = out16_
        return output

    @property
    def config(self):
        return self._config

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "simple.extendable.resources.internaldafny.impl_Compile._default"
    @staticmethod
    def DefaultSimpleExtendableResourcesConfig():
        return simple.extendable.resources.internaldafny.types.SimpleExtendableResourcesConfig_SimpleExtendableResourcesConfig()

    @staticmethod
    def SimpleExtendableResources(config):
        res: Wrappers_Compile.Result = None
        d_94_internalConfig_: SimpleExtendableResourcesOperations_Compile.Config
        d_94_internalConfig_ = SimpleExtendableResourcesOperations_Compile.Config_Config()
        d_95_client_: simple.extendable.resources.internaldafny.impl.SimpleExtendableResourcesClient
        nw3_ = simple.extendable.resources.internaldafny.impl.SimpleExtendableResourcesClient()
        nw3_.ctor__(d_94_internalConfig_)
        d_95_client_ = nw3_
        res = Wrappers_Compile.Result_Success(d_95_client_)
        return res
        return res

