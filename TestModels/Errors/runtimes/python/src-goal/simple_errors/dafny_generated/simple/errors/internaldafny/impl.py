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
import SimpleErrorsImpl_Compile

assert "simple.errors.internaldafny.impl" == __name__

class SimpleErrorsClient(simple.errors.internaldafny.types.ISimpleErrorsClient):
    def  __init__(self):
        self._config: SimpleErrorsImpl_Compile.Config = SimpleErrorsImpl_Compile.Config_Config.default()()
        pass

    def __dafnystr__(self) -> str:
        return "simple.errors.internaldafny.impl_Compile.SimpleErrorsClient"
    def ctor__(self, config):
        (self)._config = config

    def AlwaysError(self, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.errors.internaldafny.types.GetErrorsOutput.default())()
        out0_: Wrappers_Compile.Result
        out0_ = SimpleErrorsImpl_Compile.default__.AlwaysError((self).config, input)
        output = out0_
        return output

    def AlwaysMultipleErrors(self, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.errors.internaldafny.types.GetErrorsOutput.default())()
        out1_: Wrappers_Compile.Result
        out1_ = SimpleErrorsImpl_Compile.default__.AlwaysMultipleErrors((self).config, input)
        output = out1_
        print("AlwaysMultipleErrors")
        print(output)
        return output

    def AlwaysNativeError(self, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.errors.internaldafny.types.GetErrorsOutput.default())()
        out2_: Wrappers_Compile.Result
        out2_ = SimpleErrorsImpl_Compile.default__.AlwaysNativeError((self).config, input)
        output = out2_
        return output

    @property
    def config(self):
        return self._config

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "simple.errors.internaldafny.impl_Compile._default"
    @staticmethod
    def DefaultSimpleErrorsConfig():
        return simple.errors.internaldafny.types.SimpleErrorsConfig_SimpleErrorsConfig()

    @staticmethod
    def SimpleErrors(config):
        res: Wrappers_Compile.Result = None
        d_75_client_: simple.errors.internaldafny.impl.SimpleErrorsClient
        nw2_ = simple.errors.internaldafny.impl.SimpleErrorsClient()
        nw2_.ctor__(SimpleErrorsImpl_Compile.Config_Config())
        d_75_client_ = nw2_
        res = Wrappers_Compile.Result_Success(d_75_client_)
        return res
        return res

