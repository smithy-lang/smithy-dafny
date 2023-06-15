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
import simple.types.boolean.internaldafny.types

assert "SimpleBooleanImpl_Compile" == __name__
SimpleBooleanImpl_Compile = sys.modules[__name__]

class Config:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [Config_Config()]
    @classmethod
    def default(cls, ):
        return lambda: Config_Config()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Config(self) -> bool:
        return isinstance(self, SimpleBooleanImpl_Compile.Config_Config)

class Config_Config(Config, NamedTuple('Config', [])):
    def __dafnystr__(self) -> str:
        return f'SimpleBooleanImpl_Compile.Config.Config'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, SimpleBooleanImpl_Compile.Config_Config)
    def __hash__(self) -> int:
        return super().__hash__()


class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "SimpleBooleanImpl_Compile._default"
    @staticmethod
    def GetBoolean(config, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.types.boolean.internaldafny.types.GetBooleanOutput.default())()
        if not(((input).value).is_Some):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/src/SimpleBooleanImpl.dfy(17,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not(((((input).value).value) == (True)) or ((((input).value).value) == (False))):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/src/SimpleBooleanImpl.dfy(19,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        d_71_res_: simple.types.boolean.internaldafny.types.GetBooleanOutput
        d_71_res_ = simple.types.boolean.internaldafny.types.GetBooleanOutput_GetBooleanOutput((input).value)
        if not(((((d_71_res_).value).value) == (True)) or ((((d_71_res_).value).value) == (False))):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/src/SimpleBooleanImpl.dfy(22,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not((((input).value).value) == (((d_71_res_).value).value)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/src/SimpleBooleanImpl.dfy(24,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        output = Wrappers_Compile.Result_Success(d_71_res_)
        return output
        return output

