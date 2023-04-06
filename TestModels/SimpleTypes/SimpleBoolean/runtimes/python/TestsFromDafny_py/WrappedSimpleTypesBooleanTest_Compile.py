import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import SimpleBooleanImplTest_Compile
import Dafny.Simpletypes.Boolean.Wrapped

assert "WrappedSimpleTypesBooleanTest_Compile" == __name__
WrappedSimpleTypesBooleanTest_Compile = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "WrappedSimpleTypesBooleanTest_Compile._default"
    @staticmethod
    def GetBooleanTrue():
        d_8_client_: Dafny.Simpletypes.Boolean.Types.ISimpleBooleanClient
        d_9_valueOrError0_: Wrappers_Compile.Result = None
        out4_: Wrappers_Compile.Result
        out4_ = Dafny.Simpletypes.Boolean.Wrapped.default__.WrappedSimpleBoolean(Dafny.Simpletypes.Boolean.Wrapped.default__.WrappedDefaultSimpleBooleanConfig())
        d_9_valueOrError0_ = out4_
        print(f"this is {d_9_valueOrError0_}")
        if not(not((d_9_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/test/WrappedSimpleBooleanTest.dfy(9,19): " + _dafny.string_of(d_9_valueOrError0_)
            )
        d_8_client_ = (d_9_valueOrError0_).Extract()
        SimpleBooleanImplTest_Compile.default__.TestGetBooleanTrue(d_8_client_)

    @staticmethod
    def GetBooleanFalse():
        d_10_client_: Dafny.Simpletypes.Boolean.Types.ISimpleBooleanClient
        d_11_valueOrError0_: Wrappers_Compile.Result = None
        out5_: Wrappers_Compile.Result
        out5_ = Dafny.Simpletypes.Boolean.Wrapped.default__.WrappedSimpleBoolean(Dafny.Simpletypes.Boolean.Wrapped.default__.WrappedDefaultSimpleBooleanConfig())
        d_11_valueOrError0_ = out5_
        if not(not((d_11_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/test/WrappedSimpleBooleanTest.dfy(13,19): " + _dafny.string_of(d_11_valueOrError0_)
            )
        d_10_client_ = (d_11_valueOrError0_).Extract()
        SimpleBooleanImplTest_Compile.default__.TestGetBooleanFalse(d_10_client_)

