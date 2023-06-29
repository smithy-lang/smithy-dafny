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
import SimpleRefinementImpl_Compile

assert "simple.refinement.internaldafny.impl" == __name__

class SimpleRefinementClient(simple.refinement.internaldafny.types.ISimpleRefinementClient):
    def  __init__(self):
        self._config: SimpleRefinementImpl_Compile.Config = SimpleRefinementImpl_Compile.Config_Config.default()()
        pass

    def __dafnystr__(self) -> str:
        return "simple.refinement.internaldafny.impl_Compile.SimpleRefinementClient"
    def ctor__(self, config):
        (self)._config = config

    def GetRefinement(self, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.refinement.internaldafny.types.GetRefinementOutput.default())()
        out0_: Wrappers_Compile.Result
        out0_ = SimpleRefinementImpl_Compile.default__.GetRefinement((self).config, input)
        output = out0_
        return output

    def OnlyInput(self, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(_dafny.defaults.tuple())()
        out1_: Wrappers_Compile.Result
        out1_ = SimpleRefinementImpl_Compile.default__.OnlyInput((self).config, input)
        output = out1_
        return output

    def OnlyOutput(self):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.refinement.internaldafny.types.OnlyOutputOutput.default())()
        out2_: Wrappers_Compile.Result
        out2_ = SimpleRefinementImpl_Compile.default__.OnlyOutput((self).config)
        output = out2_
        return output

    def ReadonlyOperation(self, input):
        return SimpleRefinementImpl_Compile.default__.ReadonlyOperation((self).config, input)

    @property
    def config(self):
        return self._config

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "simple.refinement.internaldafny.impl_Compile._default"
    @staticmethod
    def DefaultSimpleRefinementConfig():
        return simple.refinement.internaldafny.types.SimpleRefinementConfig_SimpleRefinementConfig()

    @staticmethod
    def SimpleRefinement(config):
        res: Wrappers_Compile.Result = None
        d_73_client_: simple.refinement.internaldafny.impl.SimpleRefinementClient
        nw1_ = simple.refinement.internaldafny.impl.SimpleRefinementClient()
        nw1_.ctor__(SimpleRefinementImpl_Compile.Config_Config())
        d_73_client_ = nw1_
        res = Wrappers_Compile.Result_Success(d_73_client_)
        return res
        return res

