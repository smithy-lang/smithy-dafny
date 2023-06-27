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
import simple.errors.internaldafny.types

assert "SimpleErrorsImpl_Compile" == __name__
SimpleErrorsImpl_Compile = sys.modules[__name__]

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
        return isinstance(self, SimpleErrorsImpl_Compile.Config_Config)

class Config_Config(Config, NamedTuple('Config', [])):
    def __dafnystr__(self) -> str:
        return f'SimpleErrorsImpl_Compile.Config.Config'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, SimpleErrorsImpl_Compile.Config_Config)
    def __hash__(self) -> int:
        return super().__hash__()


class SomeOpaqueGeneratedTypeForTesting:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "SimpleErrorsImpl_Compile.SomeOpaqueGeneratedTypeForTesting"
    def ctor__(self):
        pass
        pass


class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "SimpleErrorsImpl_Compile._default"
    @staticmethod
    def AlwaysError(config, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.errors.internaldafny.types.GetErrorsOutput.default())()
        if not(((input).value).is_Some):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Errors/src/SimpleErrorsImpl.dfy(27,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        d_71_res_: simple.errors.internaldafny.types.Error
        d_71_res_ = simple.errors.internaldafny.types.Error_SimpleErrorsException(((input).value).value)
        output = Wrappers_Compile.Result_Failure(d_71_res_)
        return output
        return output

    @staticmethod
    def AlwaysMultipleErrors(config, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.errors.internaldafny.types.GetErrorsOutput.default())()
        if not(((input).value).is_Some):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Errors/src/SimpleErrorsImpl.dfy(40,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        d_72_res_: simple.errors.internaldafny.types.Error
        d_72_res_ = simple.errors.internaldafny.types.Error_CollectionOfErrors(_dafny.Seq([simple.errors.internaldafny.types.Error_SimpleErrorsException(((input).value).value)]), _dafny.Seq("Something"))
        output = Wrappers_Compile.Result_Failure(d_72_res_)
        return output
        return output

    @staticmethod
    def AlwaysNativeError(config, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.errors.internaldafny.types.GetErrorsOutput.default())()
        d_73_opaqueObject_: SimpleErrorsImpl_Compile.SomeOpaqueGeneratedTypeForTesting
        nw1_ = SimpleErrorsImpl_Compile.SomeOpaqueGeneratedTypeForTesting()
        nw1_.ctor__()
        d_73_opaqueObject_ = nw1_
        d_74_res_: simple.errors.internaldafny.types.Error
        d_74_res_ = simple.errors.internaldafny.types.Error_Opaque(d_73_opaqueObject_)
        output = Wrappers_Compile.Result_Failure(d_74_res_)
        return output
        return output

