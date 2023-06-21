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
import SimpleIntegerImpl_Compile
import simple.types.integer.internaldafny.impl
import simple.types.integer.internaldafny.wrapped
import SimpleIntegerImplTest_Compile

assert "WrappedSimpleTypesIntegerTest_Compile" == __name__
WrappedSimpleTypesIntegerTest_Compile = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "WrappedSimpleTypesIntegerTest_Compile._default"
    @staticmethod
    def GetInteger():
        d_85_client_: simple.types.integer.internaldafny.types.ISimpleTypesIntegerClient
        d_86_valueOrError0_: Wrappers_Compile.Result = None
        out6_: Wrappers_Compile.Result
        out6_ = simple.types.integer.internaldafny.wrapped.default__.WrappedSimpleInteger(simple.types.integer.internaldafny.wrapped.default__.WrappedDefaultSimpleIntegerConfig())
        d_86_valueOrError0_ = out6_
        if not(not((d_86_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleInteger/test/WrappedSimpleIntegerTest.dfy(11,19): " + _dafny.string_of(d_86_valueOrError0_))
        d_85_client_ = (d_86_valueOrError0_).Extract()
        SimpleIntegerImplTest_Compile.default__.TestGetInteger(d_85_client_)
        SimpleIntegerImplTest_Compile.default__.TestGetIntegerKnownValue(d_85_client_)
        SimpleIntegerImplTest_Compile.default__.TestGetIntegerEdgeCases(d_85_client_)

