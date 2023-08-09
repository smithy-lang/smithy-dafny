import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import Wrappers
import StandardLibrary_mUInt
import StandardLibrary
import UTF8
import simple_types_boolean_internaldafny_types
import SimpleBooleanImpl
import simple_types_boolean_internaldafny_impl

print(sys.modules)
import SimpleBooleanImplTest
import simple_types_boolean_internaldafny_wrapped

assert "WrappedSimpleTypesBooleanTest" == __name__
WrappedSimpleTypesBooleanTest = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def GetBooleanTrue():
        d_8_client_: simple_types_boolean_internaldafny_types.ISimpleTypesBooleanClient
        d_9_valueOrError0_: Wrappers.Result = None
        out4_: Wrappers.Result
        print(simple_types_boolean_internaldafny_wrapped)
        print(simple_types_boolean_internaldafny_wrapped.__dict__)
        out4_ = simple_types_boolean_internaldafny_wrapped.default__.WrappedSimpleBoolean(simple_types_boolean_internaldafny_wrapped.default__.WrappedDefaultSimpleBooleanConfig())
        d_9_valueOrError0_ = out4_
        if not(not((d_9_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("test/WrappedSimpleBooleanTest.dfy(11,19): " + _dafny.string_of(d_9_valueOrError0_))
        d_8_client_ = (d_9_valueOrError0_).Extract()
        SimpleBooleanImplTest.default__.TestGetBooleanTrue(d_8_client_)

    @staticmethod
    def GetBooleanFalse():
        d_10_client_: simple_types_boolean_internaldafny_types.ISimpleTypesBooleanClient
        d_11_valueOrError0_: Wrappers.Result = None
        out5_: Wrappers.Result
        out5_ = simple_types_boolean_internaldafny_wrapped.default__.WrappedSimpleBoolean(simple_types_boolean_internaldafny_wrapped.default__.WrappedDefaultSimpleBooleanConfig())
        d_11_valueOrError0_ = out5_
        if not(not((d_11_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("test/WrappedSimpleBooleanTest.dfy(15,19): " + _dafny.string_of(d_11_valueOrError0_))
        d_10_client_ = (d_11_valueOrError0_).Extract()
        SimpleBooleanImplTest.default__.TestGetBooleanFalse(d_10_client_)

