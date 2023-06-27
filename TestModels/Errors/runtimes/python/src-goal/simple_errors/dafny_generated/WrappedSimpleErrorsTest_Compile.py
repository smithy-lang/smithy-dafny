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
import simple.errors.internaldafny.impl
import simple.errors.internaldafny.wrapped
import SimpleErrorsImplTest_Compile

assert "WrappedSimpleErrorsTest_Compile" == __name__
WrappedSimpleErrorsTest_Compile = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "WrappedSimpleErrorsTest_Compile._default"
    @staticmethod
    def GetErrors():
        d_88_client_: simple.errors.internaldafny.types.ISimpleErrorsClient
        d_89_valueOrError0_: Wrappers_Compile.Result = None
        out7_: Wrappers_Compile.Result
        out7_ = simple.errors.internaldafny.wrapped.default__.WrappedSimpleErrors(simple.errors.internaldafny.wrapped.default__.WrappedDefaultSimpleErrorsConfig())
        d_89_valueOrError0_ = out7_
        if not(not((d_89_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Errors/test/WrappedSimpleErrorsTest.dfy(11,19): " + _dafny.string_of(d_89_valueOrError0_))
        d_88_client_ = (d_89_valueOrError0_).Extract()
        SimpleErrorsImplTest_Compile.default__.TestAlwaysError(d_88_client_)
        SimpleErrorsImplTest_Compile.default__.TestAlwaysMultipleErrors(d_88_client_)
        SimpleErrorsImplTest_Compile.default__.TestAlwaysNativeError(d_88_client_)

