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
import simple.refinement.internaldafny.types

assert "SimpleRefinementImpl_Compile" == __name__
SimpleRefinementImpl_Compile = sys.modules[__name__]

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
        return isinstance(self, SimpleRefinementImpl_Compile.Config_Config)

class Config_Config(Config, NamedTuple('Config', [])):
    def __dafnystr__(self) -> str:
        return f'SimpleRefinementImpl_Compile.Config.Config'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, SimpleRefinementImpl_Compile.Config_Config)
    def __hash__(self) -> int:
        return super().__hash__()


class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "SimpleRefinementImpl_Compile._default"
    @staticmethod
    def GetRefinement(config, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.refinement.internaldafny.types.GetRefinementOutput.default())()
        d_71_res_: simple.refinement.internaldafny.types.GetRefinementOutput
        d_71_res_ = simple.refinement.internaldafny.types.GetRefinementOutput_GetRefinementOutput((input).requiredString, (input).optionalString)
        output = Wrappers_Compile.Result_Success(d_71_res_)
        return output
        return output

    @staticmethod
    def OnlyInput(config, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(_dafny.defaults.tuple())()
        _dafny.print(_dafny.string_of(input))
        output = Wrappers_Compile.Result_Success(())
        return output
        return output

    @staticmethod
    def OnlyOutput(config):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.refinement.internaldafny.types.OnlyOutputOutput.default())()
        d_72_res_: simple.refinement.internaldafny.types.OnlyOutputOutput
        d_72_res_ = simple.refinement.internaldafny.types.OnlyOutputOutput_OnlyOutputOutput(Wrappers_Compile.Option_Some(_dafny.Seq("Hello World")))
        output = Wrappers_Compile.Result_Success(d_72_res_)
        return output
        return output

    @staticmethod
    def ReadonlyOperation(config, input):
        return Wrappers_Compile.Result_Success(simple.refinement.internaldafny.types.ReadonlyOperationOutput_ReadonlyOperationOutput((input).requiredString, (input).optionalString))

