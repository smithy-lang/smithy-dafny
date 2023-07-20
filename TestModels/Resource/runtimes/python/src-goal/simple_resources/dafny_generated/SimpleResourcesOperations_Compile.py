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

assert "SimpleResourcesOperations_Compile" == __name__
SimpleResourcesOperations_Compile = sys.modules[__name__]

class Config:
    @classmethod
    def default(cls, ):
        return lambda: Config_Config(_dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Config(self) -> bool:
        return isinstance(self, SimpleResourcesOperations_Compile.Config_Config)

class Config_Config(Config, NamedTuple('Config', [('name', Any)])):
    def __dafnystr__(self) -> str:
        return f'SimpleResourcesOperations_Compile.Config.Config({_dafny.string_of(self.name)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, SimpleResourcesOperations_Compile.Config_Config) and self.name == __o.name
    def __hash__(self) -> int:
        return super().__hash__()


class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "SimpleResourcesOperations_Compile._default"
    @staticmethod
    def ValidInternalConfig_q(config):
        return (True) and ((len((config).name)) > (0))

    @staticmethod
    def GetResources(config, input):
        print("ops_compile")
        output: Wrappers_Compile.Result = None
        d_73_resource_: SimpleResource_Compile.SimpleResource
        nw1_ = SimpleResource_Compile.SimpleResource()
        nw1_.ctor__((input).value, (config).name)
        d_73_resource_ = nw1_
        d_74_result_: simple.resources.internaldafny.types.GetResourcesOutput
        d_74_result_ = simple.resources.internaldafny.types.GetResourcesOutput_GetResourcesOutput(d_73_resource_)
        output = Wrappers_Compile.Result_Success(d_74_result_)
        print("ret ops_compile")
        print(nw1_)
        return output
        return output

