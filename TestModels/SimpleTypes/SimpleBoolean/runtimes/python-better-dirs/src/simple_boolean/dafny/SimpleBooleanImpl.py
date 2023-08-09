import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

# from . import module_
import _dafny
import System_
import Wrappers
import StandardLibrary_mUInt
import StandardLibrary
import UTF8
import simple_types_boolean_internaldafny_types

# assert "SimpleBooleanImpl" == __name__
SimpleBooleanImpl = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def GetBoolean(config, input):
        output: Wrappers.Result = Wrappers.Result.default(
          simple_types_boolean_internaldafny_types.GetBooleanOutput.default())()
        if not(((input).value).is_Some):
            raise _dafny.HaltException("src/SimpleBooleanImpl.dfy(17,4): " + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "expectation violation"))).VerbatimString(False))
        if not(((((input).value).value) == (True)) or ((((input).value).value) == (False))):
            raise _dafny.HaltException("src/SimpleBooleanImpl.dfy(19,4): " + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "expectation violation"))).VerbatimString(False))
        d_0_res_: simple_types_boolean_internaldafny_types.GetBooleanOutput
        d_0_res_ = simple_types_boolean_internaldafny_types.GetBooleanOutput_GetBooleanOutput((input).value)
        if not(((((d_0_res_).value).value) == (True)) or ((((d_0_res_).value).value) == (False))):
            raise _dafny.HaltException("src/SimpleBooleanImpl.dfy(22,4): " + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "expectation violation"))).VerbatimString(False))
        if not((((input).value).value) == (((d_0_res_).value).value)):
            raise _dafny.HaltException("src/SimpleBooleanImpl.dfy(24,4): " + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "expectation violation"))).VerbatimString(False))
        output = Wrappers.Result_Success(d_0_res_)
        return output
        return output


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
        return isinstance(self, SimpleBooleanImpl.Config_Config)

class Config_Config(Config, NamedTuple('Config', [])):
    def __dafnystr__(self) -> str:
        return f'SimpleBooleanImpl.Config.Config'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, SimpleBooleanImpl.Config_Config)
    def __hash__(self) -> int:
        return super().__hash__()

