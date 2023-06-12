import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import simple.types.boolean.internaldafny.types
import SimpleBooleanImpl_Compile

import Wrappers_Compile

assert "simple.types.boolean.internaldafny.impl" == __name__

class SimpleBooleanClient(simple.types.boolean.internaldafny.types.ISimpleBooleanClient):
    def  __init__(self):
        self._config: SimpleBooleanImpl_Compile.Config = SimpleBooleanImpl_Compile.Config_Config.default()()
        pass

    def __dafnystr__(self) -> str:
        return "simple.types.boolean.internaldafny.impl_Compile.SimpleBooleanClient"
    def ctor__(self, config):
        (self)._config = config

    def GetBoolean(self, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.types.boolean.internaldafny.types.GetBooleanOutput.default())()
        out0_: Wrappers_Compile.Result
        out0_ = SimpleBooleanImpl_Compile.default__.GetBoolean((self).config, input)
        output = out0_
        return output

    @property
    def config(self):
        return self._config

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "simple.types.boolean.internaldafny.impl_Compile._default"
    @staticmethod
    def DefaultSimpleBooleanConfig():
        return simple.types.boolean.internaldafny.types.SimpleBooleanConfig_SimpleBooleanConfig()

    @staticmethod
    def SimpleBoolean(config):
        res: Wrappers_Compile.Result = None
        d_1_client_: simple.types.boolean.internaldafny.impl.SimpleBooleanClient
        nw0_ = simple.types.boolean.internaldafny.impl.SimpleBooleanClient()
        nw0_.ctor__(SimpleBooleanImpl_Compile.Config_Config())
        d_1_client_ = nw0_
        res = Wrappers_Compile.Result_Success(d_1_client_)
        return res
        return res

