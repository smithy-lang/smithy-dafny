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

assert "simple.resources.internaldafny.impl" == __name__

class SimpleResourcesClient(simple.resources.internaldafny.types.ISimpleResourcesClient):
    def  __init__(self):
        self._config: SimpleResourcesOperations_Compile.Config = SimpleResourcesOperations_Compile.Config_Config.default()()
        pass

    def __dafnystr__(self) -> str:
        return "simple.resources.internaldafny.impl_Compile.SimpleResourcesClient"
    def ctor__(self, config):
        (self)._config = config

    def GetResources(self, input):
        print("impl")
        output: Wrappers_Compile.Result = None
        out2_: Wrappers_Compile.Result
        out2_ = SimpleResourcesOperations_Compile.default__.GetResources((self).config, input)
        output = out2_
        return output

    @property
    def config(self):
        return self._config

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "simple.resources.internaldafny.impl_Compile._default"
    @staticmethod
    def DefaultSimpleResourcesConfig():
        return simple.resources.internaldafny.types.SimpleResourcesConfig_SimpleResourcesConfig(_dafny.Seq("default"))

    @staticmethod
    def SimpleResources(config):
        res: Wrappers_Compile.Result = None
        d_75_internalConfig_: SimpleResourcesOperations_Compile.Config
        d_75_internalConfig_ = SimpleResourcesOperations_Compile.Config_Config((config).name)
        if SimpleResourcesOperations_Compile.default__.ValidInternalConfig_q(d_75_internalConfig_):
            d_76_client_: simple.resources.internaldafny.impl.SimpleResourcesClient
            nw2_ = simple.resources.internaldafny.impl.SimpleResourcesClient()
            nw2_.ctor__(d_75_internalConfig_)
            d_76_client_ = nw2_
            res = Wrappers_Compile.Result_Success(d_76_client_)
            return res
        elif True:
            res = Wrappers_Compile.Result_Failure(simple.resources.internaldafny.types.Error_SimpleResourcesException(_dafny.Seq("Length of name must be greater than 0")))
            return res
        return res

