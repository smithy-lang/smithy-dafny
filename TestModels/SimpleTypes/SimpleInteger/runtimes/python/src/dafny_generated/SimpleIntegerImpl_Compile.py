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

assert "SimpleIntegerImpl_Compile" == __name__
SimpleIntegerImpl_Compile = sys.modules[__name__]

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
        return isinstance(self, SimpleIntegerImpl_Compile.Config_Config)

class Config_Config(Config, NamedTuple('Config', [])):
    def __dafnystr__(self) -> str:
        return f'SimpleIntegerImpl_Compile.Config.Config'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, SimpleIntegerImpl_Compile.Config_Config)
    def __hash__(self) -> int:
        return super().__hash__()


class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "SimpleIntegerImpl_Compile._default"
    @staticmethod
    def GetInteger(config, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.types.integer.internaldafny.types.GetIntegerOutput.default())()
        if not(((input).value).is_Some):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleInteger/src/SimpleIntegerImpl.dfy(20,8): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not((((0) - ((StandardLibrary_mUInt_Compile.default__).INT32__MAX__LIMIT)) <= (((input).value).UnwrapOr(0))) and ((((input).value).UnwrapOr(0)) <= (((StandardLibrary_mUInt_Compile.default__).INT32__MAX__LIMIT) - (1)))):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleInteger/src/SimpleIntegerImpl.dfy(21,8): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        d_71_res_: simple.types.integer.internaldafny.types.GetIntegerOutput
        d_71_res_ = simple.types.integer.internaldafny.types.GetIntegerOutput_GetIntegerOutput((input).value)
        output = Wrappers_Compile.Result_Success(d_71_res_)
        return output
        return output

    @staticmethod
    def GetIntegerKnownValueTest(config, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.types.integer.internaldafny.types.GetIntegerOutput.default())()
        if not(((input).value).is_Some):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleInteger/src/SimpleIntegerImpl.dfy(27,8): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not((((input).value).UnwrapOr(0)) == (20)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleInteger/src/SimpleIntegerImpl.dfy(28,8): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        d_72_res_: simple.types.integer.internaldafny.types.GetIntegerOutput
        d_72_res_ = simple.types.integer.internaldafny.types.GetIntegerOutput_GetIntegerOutput((input).value)
        output = Wrappers_Compile.Result_Success(d_72_res_)
        return output
        return output

