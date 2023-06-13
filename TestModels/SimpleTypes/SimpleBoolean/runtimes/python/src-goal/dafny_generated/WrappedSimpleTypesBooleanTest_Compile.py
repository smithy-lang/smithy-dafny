import sys
from math import floor
from itertools import count

import _dafny
import System_
import SimpleBooleanImplTest_Compile
import simple.types.boolean.internaldafny.wrapped

import Extern

assert "WrappedSimpleTypesBooleanTest_Compile" == __name__
WrappedSimpleTypesBooleanTest_Compile = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "WrappedSimpleTypesBooleanTest_Compile._default"
    @staticmethod
    def GetBooleanTrue():
        d_8_client_: simple.types.boolean.internaldafny.types.ISimpleBooleanClient
        d_9_valueOrError0_: Wrappers_Compile.Result = None
        out4_: Wrappers_Compile.Result
        out4_ = simple.types.boolean.internaldafny.wrapped.default__.WrappedSimpleBoolean(simple.types.boolean.internaldafny.wrapped.default__.WrappedDefaultSimpleBooleanConfig())
        d_9_valueOrError0_ = out4_
        if not(not((d_9_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/test/WrappedSimpleBooleanTest.dfy(11,19): " + _dafny.string_of(d_9_valueOrError0_))
        d_8_client_ = (d_9_valueOrError0_).Extract()
        SimpleBooleanImplTest_Compile.default__.TestGetBooleanTrue(d_8_client_)

    @staticmethod
    def GetBooleanFalse():
        d_10_client_: simple.types.boolean.internaldafny.types.ISimpleBooleanClient
        d_11_valueOrError0_: Wrappers_Compile.Result = None
        out5_: Wrappers_Compile.Result
        out5_ = simple.types.boolean.internaldafny.wrapped.default__.WrappedSimpleBoolean(simple.types.boolean.internaldafny.wrapped.default__.WrappedDefaultSimpleBooleanConfig())
        d_11_valueOrError0_ = out5_
        if not(not((d_11_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/test/WrappedSimpleBooleanTest.dfy(15,19): " + _dafny.string_of(d_11_valueOrError0_))
        d_10_client_ = (d_11_valueOrError0_).Extract()
        SimpleBooleanImplTest_Compile.default__.TestGetBooleanFalse(d_10_client_)

