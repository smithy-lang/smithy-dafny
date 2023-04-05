import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
from . import Types
import Dafny.Simpletypes.Boolean
import SimpleBooleanImpl_Compile
import Wrappers_Compile

assert "Dafny.Simpletypes.Boolean" == __name__
Dafny.Simpletypes.Boolean = sys.modules[__name__]

class SimpleBooleanClient(Dafny.Simpletypes.Boolean.Types.ISimpleBooleanClient):
    def  __init__(self):
        self._config: SimpleBooleanImpl_Compile.Config = SimpleBooleanImpl_Compile.Config_Config.default()()
        pass

    def __dafnystr__(self) -> str:
        return "Dafny.Simpletypes.Boolean_Compile.SimpleBooleanClient"
    def ctor__(self, config):
        (self)._config = config

    def GetBoolean(self, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(Dafny.Simpletypes.Boolean.Types.GetBooleanOutput.default())()
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
        return "Dafny.Simpletypes.Boolean_Compile._default"
    @staticmethod
    def DefaultSimpleBooleanConfig():
        return Dafny.Simpletypes.Boolean.Types.SimpleBooleanConfig_SimpleBooleanConfig()

    @staticmethod
    def SimpleBoolean(config):
        res: Wrappers_Compile.Result = None
        d_1_client_: Dafny.Simpletypes.Boolean.SimpleBooleanClient
        nw0_ = Dafny.Simpletypes.Boolean.SimpleBooleanClient()
        nw0_.ctor__(SimpleBooleanImpl_Compile.Config_Config())
        d_1_client_ = nw0_
        res = Wrappers_Compile.Result_Success(d_1_client_)
        return res
        return res

