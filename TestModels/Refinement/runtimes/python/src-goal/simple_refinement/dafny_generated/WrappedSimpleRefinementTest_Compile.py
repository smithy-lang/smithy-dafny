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
import simple.refinement.internaldafny.impl
import simple.refinement.internaldafny.wrapped
import SimpleRefinementImplTest_Compile

assert "WrappedSimpleRefinementTest_Compile" == __name__
WrappedSimpleRefinementTest_Compile = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "WrappedSimpleRefinementTest_Compile._default"
    @staticmethod
    def Refinement():
        d_84_client_: simple.refinement.internaldafny.types.ISimpleRefinementClient
        d_85_valueOrError0_: Wrappers_Compile.Result = None
        out7_: Wrappers_Compile.Result
        out7_ = simple.refinement.internaldafny.wrapped.default__.WrappedSimpleRefinement(simple.refinement.internaldafny.wrapped.default__.WrappedDefaultSimpleRefinementConfig())
        d_85_valueOrError0_ = out7_
        if not(not((d_85_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Refinement/test/WrappedSimpleRefinementImplTest.dfy(11,19): " + _dafny.string_of(d_85_valueOrError0_))
        d_84_client_ = (d_85_valueOrError0_).Extract()
        SimpleRefinementImplTest_Compile.default__.TestGetRefinement(d_84_client_)
        SimpleRefinementImplTest_Compile.default__.TestOnlyInput(d_84_client_)
        SimpleRefinementImplTest_Compile.default__.TestOnlyOutput(d_84_client_)
        SimpleRefinementImplTest_Compile.default__.TestReadonlyOperation(d_84_client_)

