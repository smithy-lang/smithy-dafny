import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import simple.types.boolean.internaldafny

import module_
import _dafny
import System_
import Wrappers_Compile

assert "SimpleBooleanImplTest_Compile" == __name__
SimpleBooleanImplTest_Compile = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "SimpleBooleanImplTest_Compile._default"
    @staticmethod
    def GetBooleanTrue():
        d_0_client_: simple.types.boolean.internaldafny.SimpleBooleanClient
        d_1_valueOrError0_: Wrappers_Compile.Result = None
        out0_: Wrappers_Compile.Result
        out0_ = simple.types.boolean.internaldafny.default__.SimpleBoolean(simple.types.boolean.internaldafny.default__.DefaultSimpleBooleanConfig())
        d_1_valueOrError0_ = out0_
        if not(not((d_1_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/test/SimpleBooleanImplTest.dfy(10,19): " + _dafny.string_of(d_1_valueOrError0_))
        d_0_client_ = (d_1_valueOrError0_).Extract()
        SimpleBooleanImplTest_Compile.default__.TestGetBooleanTrue(d_0_client_)

    @staticmethod
    def GetBooleanFalse():
        d_2_client_: simple.types.boolean.internaldafny.SimpleBooleanClient
        d_3_valueOrError0_: Wrappers_Compile.Result = None
        out1_: Wrappers_Compile.Result
        out1_ = simple.types.boolean.internaldafny.default__.SimpleBoolean(simple.types.boolean.internaldafny.default__.DefaultSimpleBooleanConfig())
        d_3_valueOrError0_ = out1_
        if not(not((d_3_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/test/SimpleBooleanImplTest.dfy(14,19): " + _dafny.string_of(d_3_valueOrError0_))
        d_2_client_ = (d_3_valueOrError0_).Extract()
        SimpleBooleanImplTest_Compile.default__.TestGetBooleanFalse(d_2_client_)

    @staticmethod
    def TestGetBooleanTrue(client):
        d_4_ret_: simple.types.boolean.internaldafny.types.GetBooleanOutput
        d_5_valueOrError0_: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.types.boolean.internaldafny.types.GetBooleanOutput.default())()
        out2_: Wrappers_Compile.Result
        out2_ = (client).GetBoolean(simple.types.boolean.internaldafny.types.GetBooleanInput_GetBooleanInput(Wrappers_Compile.Option_Some(True)))
        d_5_valueOrError0_ = out2_
        if not(not((d_5_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/test/SimpleBooleanImplTest.dfy(23,16): " + _dafny.string_of(d_5_valueOrError0_))
        d_4_ret_ = (d_5_valueOrError0_).Extract()
        if not((((d_4_ret_).value).UnwrapOr(False)) == (True)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/test/SimpleBooleanImplTest.dfy(24,8): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        _dafny.print(_dafny.string_of(d_4_ret_))

    @staticmethod
    def TestGetBooleanFalse(client):
        d_6_ret_: simple.types.boolean.internaldafny.types.GetBooleanOutput
        d_7_valueOrError0_: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.types.boolean.internaldafny.types.GetBooleanOutput.default())()
        out3_: Wrappers_Compile.Result
        out3_ = (client).GetBoolean(simple.types.boolean.internaldafny.types.GetBooleanInput_GetBooleanInput(Wrappers_Compile.Option_Some(False)))
        d_7_valueOrError0_ = out3_
        if not(not((d_7_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/test/SimpleBooleanImplTest.dfy(33,16): " + _dafny.string_of(d_7_valueOrError0_))
        d_6_ret_ = (d_7_valueOrError0_).Extract()
        if not((((d_6_ret_).value).UnwrapOr(True)) == (False)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/test/SimpleBooleanImplTest.dfy(34,8): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        _dafny.print(_dafny.string_of(d_6_ret_))

