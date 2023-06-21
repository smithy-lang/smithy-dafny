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
import simple.types.integer.internaldafny.types
import SimpleIntegerImpl_Compile

assert "simple.types.integer.internaldafny.impl" == __name__

class SimpleIntegerClient(simple.types.integer.internaldafny.types.ISimpleTypesIntegerClient):
    def  __init__(self):
        self._config: SimpleIntegerImpl_Compile.Config = SimpleIntegerImpl_Compile.Config_Config.default()()
        pass

    def __dafnystr__(self) -> str:
        return "simple.types.integer.internaldafny.impl_Compile.SimpleIntegerClient"
    def ctor__(self, config):
        (self)._config = config

    def GetInteger(self, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.types.integer.internaldafny.types.GetIntegerOutput.default())()
        out0_: Wrappers_Compile.Result
        out0_ = SimpleIntegerImpl_Compile.default__.GetInteger((self).config, input)
        output = out0_
        return output

    def GetIntegerKnownValueTest(self, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.types.integer.internaldafny.types.GetIntegerOutput.default())()
        out1_: Wrappers_Compile.Result
        out1_ = SimpleIntegerImpl_Compile.default__.GetIntegerKnownValueTest((self).config, input)
        output = out1_
        return output

    @property
    def config(self):
        return self._config

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "simple.types.integer.internaldafny.impl_Compile._default"
    @staticmethod
    def DefaultSimpleIntegerConfig():
        return simple.types.integer.internaldafny.types.SimpleIntegerConfig_SimpleIntegerConfig()

    @staticmethod
    def SimpleInteger(config):
        res: Wrappers_Compile.Result = None
        d_73_client_: simple.types.integer.internaldafny.impl.SimpleIntegerClient
        nw1_ = simple.types.integer.internaldafny.impl.SimpleIntegerClient()
        nw1_.ctor__(SimpleIntegerImpl_Compile.Config_Config())
        d_73_client_ = nw1_
        res = Wrappers_Compile.Result_Success(d_73_client_)
        return res
        return res

