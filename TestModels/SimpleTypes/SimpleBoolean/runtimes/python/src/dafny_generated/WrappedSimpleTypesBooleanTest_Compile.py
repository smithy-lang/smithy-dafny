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
import simple.types.boolean.internaldafny.types
import SimpleBooleanImpl_Compile
import simple.types.boolean.internaldafny.impl
import SimpleBooleanImplTest_Compile
import simple.types.boolean.internaldafny.wrapped

assert "WrappedSimpleTypesBooleanTest_Compile" == __name__
WrappedSimpleTypesBooleanTest_Compile = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "WrappedSimpleTypesBooleanTest_Compile._default"
    @staticmethod
    def GetBooleanTrue():
        d_81_client_: simple.types.boolean.internaldafny.types.ISimpleBooleanClient
        d_82_valueOrError0_: Wrappers_Compile.Result = None
        out5_: Wrappers_Compile.Result
        out5_ = simple.types.boolean.internaldafny.wrapped.default__.WrappedSimpleBoolean(simple.types.boolean.internaldafny.wrapped.default__.WrappedDefaultSimpleBooleanConfig())
        d_82_valueOrError0_ = out5_
        if not(not((d_82_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/test/WrappedSimpleBooleanTest.dfy(11,19): " + _dafny.string_of(d_82_valueOrError0_))
        d_81_client_ = (d_82_valueOrError0_).Extract()
        SimpleBooleanImplTest_Compile.default__.TestGetBooleanTrue(d_81_client_)

    @staticmethod
    def GetBooleanFalse():
        d_83_client_: simple.types.boolean.internaldafny.types.ISimpleBooleanClient
        d_84_valueOrError0_: Wrappers_Compile.Result = None
        out6_: Wrappers_Compile.Result
        out6_ = simple.types.boolean.internaldafny.wrapped.default__.WrappedSimpleBoolean(simple.types.boolean.internaldafny.wrapped.default__.WrappedDefaultSimpleBooleanConfig())
        d_84_valueOrError0_ = out6_
        if not(not((d_84_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/test/WrappedSimpleBooleanTest.dfy(15,19): " + _dafny.string_of(d_84_valueOrError0_))
        d_83_client_ = (d_84_valueOrError0_).Extract()
        SimpleBooleanImplTest_Compile.default__.TestGetBooleanFalse(d_83_client_)

