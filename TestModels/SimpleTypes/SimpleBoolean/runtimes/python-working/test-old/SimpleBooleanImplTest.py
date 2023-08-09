import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
# import Wrappers
import StandardLibrary_mUInt
import StandardLibrary
import UTF8
import simple_boolean.simple.types.boolean.internaldafny.types
import simple_boolean.SimpleBooleanImpl
import simple_boolean.simple.types.boolean.internaldafny.impl

assert "SimpleBooleanImplTest" == __name__
SimpleBooleanImplTest = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def GetBooleanTrue():
        d_0_client_: simple.types.boolean.internaldafny.impl.SimpleBooleanClient
        d_1_valueOrError0_: Wrappers.Result = None
        out0_: Wrappers.Result
        out0_ = simple.types.boolean.internaldafny.impl.default__.SimpleBoolean(simple.types.boolean.internaldafny.impl.default__.DefaultSimpleBooleanConfig())
        d_1_valueOrError0_ = out0_
        if not(not((d_1_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("test/SimpleBooleanImplTest.dfy(10,19): " + _dafny.string_of(d_1_valueOrError0_))
        d_0_client_ = (d_1_valueOrError0_).Extract()
        SimpleBooleanImplTest.default__.TestGetBooleanTrue(d_0_client_)

    @staticmethod
    def GetBooleanFalse():
        d_2_client_: simple.types.boolean.internaldafny.impl.SimpleBooleanClient
        d_3_valueOrError0_: Wrappers.Result = None
        out1_: Wrappers.Result
        out1_ = simple.types.boolean.internaldafny.impl.default__.SimpleBoolean(simple.types.boolean.internaldafny.impl.default__.DefaultSimpleBooleanConfig())
        d_3_valueOrError0_ = out1_
        if not(not((d_3_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("test/SimpleBooleanImplTest.dfy(14,19): " + _dafny.string_of(d_3_valueOrError0_))
        d_2_client_ = (d_3_valueOrError0_).Extract()
        SimpleBooleanImplTest.default__.TestGetBooleanFalse(d_2_client_)

    @staticmethod
    def TestGetBooleanTrue(client):
        d_4_ret_: simple.types.boolean.internaldafny.types.GetBooleanOutput
        d_5_valueOrError0_: Wrappers.Result = Wrappers.Result_Success.default(simple.types.boolean.internaldafny.types.GetBooleanOutput.default())()
        out2_: Wrappers.Result
        out2_ = (client).GetBoolean(simple.types.boolean.internaldafny.types.GetBooleanInput_GetBooleanInput(Wrappers.Option_Some(True)))
        d_5_valueOrError0_ = out2_
        if not(not((d_5_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("test/SimpleBooleanImplTest.dfy(23,16): " + _dafny.string_of(d_5_valueOrError0_))
        d_4_ret_ = (d_5_valueOrError0_).Extract()
        if not((((d_4_ret_).value).UnwrapOr(False)) == (True)):
            raise _dafny.HaltException("test/SimpleBooleanImplTest.dfy(24,8): " + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "expectation violation"))).VerbatimString(False))
        _dafny.print(_dafny.string_of(d_4_ret_))

    @staticmethod
    def TestGetBooleanFalse(client):
        d_6_ret_: simple.types.boolean.internaldafny.types.GetBooleanOutput
        d_7_valueOrError0_: Wrappers.Result = Wrappers.Result_Success.default(simple.types.boolean.internaldafny.types.GetBooleanOutput.default())()
        out3_: Wrappers.Result
        out3_ = (client).GetBoolean(simple.types.boolean.internaldafny.types.GetBooleanInput_GetBooleanInput(Wrappers.Option_Some(False)))
        d_7_valueOrError0_ = out3_
        if not(not((d_7_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("test/SimpleBooleanImplTest.dfy(33,16): " + _dafny.string_of(d_7_valueOrError0_))
        d_6_ret_ = (d_7_valueOrError0_).Extract()
        if not((((d_6_ret_).value).UnwrapOr(True)) == (False)):
            raise _dafny.HaltException("test/SimpleBooleanImplTest.dfy(34,8): " + (_dafny.SeqWithoutIsStrInference(map(_dafny.CodePoint, "expectation violation"))).VerbatimString(False))
        _dafny.print(_dafny.string_of(d_6_ret_))

