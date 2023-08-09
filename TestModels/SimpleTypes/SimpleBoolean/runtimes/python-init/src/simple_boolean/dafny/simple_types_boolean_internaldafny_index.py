import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import Wrappers
import StandardLibrary_mUInt
import StandardLibrary
import UTF8
import simple_types_boolean_internaldafny_types
import SimpleBooleanImpl

assert "simple_types_boolean_internaldafny_index" == __name__
simple_types_boolean_internaldafny_index = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def DefaultSimpleBooleanConfig():
        return simple_types_boolean_internaldafny_types.SimpleBooleanConfig_SimpleBooleanConfig()

    @staticmethod
    def SimpleBoolean(config):
        res: Wrappers.Result = None
        d_1_client_: simple_types_boolean_internaldafny_index.SimpleBooleanClient
        nw0_ = simple_types_boolean_internaldafny_index.SimpleBooleanClient()
        nw0_.ctor__(SimpleBooleanImpl.Config_Config())
        d_1_client_ = nw0_
        res = Wrappers.Result_Success(d_1_client_)
        return res
        return res


class SimpleBooleanClient(simple_types_boolean_internaldafny_types.ISimpleTypesBooleanClient):
    def  __init__(self):
        self._config: SimpleBooleanImpl.Config = SimpleBooleanImpl.Config.default()()
        pass

    def __dafnystr__(self) -> str:
        return "SimpleBoolean.SimpleBooleanClient"
    def ctor__(self, config):
        (self)._config = config

    def GetBoolean(self, input):
        output: Wrappers.Result = Wrappers.Result.default(simple_types_boolean_internaldafny_types.GetBooleanOutput.default())()
        out0_: Wrappers.Result
        out0_ = SimpleBooleanImpl.default__.GetBoolean((self).config, input)
        output = out0_
        return output

    @property
    def config(self):
        return self._config
