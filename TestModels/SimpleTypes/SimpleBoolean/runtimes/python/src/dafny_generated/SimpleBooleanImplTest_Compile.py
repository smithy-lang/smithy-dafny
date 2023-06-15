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

assert "SimpleBooleanImplTest_Compile" == __name__
SimpleBooleanImplTest_Compile = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "SimpleBooleanImplTest_Compile._default"
    @staticmethod
    def GetBooleanTrue():
        d_73_client_: simple.types.boolean.internaldafny.impl.SimpleBooleanClient
        d_74_valueOrError0_: Wrappers_Compile.Result = None
        out1_: Wrappers_Compile.Result
        out1_ = simple.types.boolean.internaldafny.impl.default__.SimpleBoolean(simple.types.boolean.internaldafny.impl.default__.DefaultSimpleBooleanConfig())
        d_74_valueOrError0_ = out1_
        if not(not((d_74_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/test/SimpleBooleanImplTest.dfy(10,19): " + _dafny.string_of(d_74_valueOrError0_))
        d_73_client_ = (d_74_valueOrError0_).Extract()
        SimpleBooleanImplTest_Compile.default__.TestGetBooleanTrue(d_73_client_)

    @staticmethod
    def GetBooleanFalse():
        d_75_client_: simple.types.boolean.internaldafny.impl.SimpleBooleanClient
        d_76_valueOrError0_: Wrappers_Compile.Result = None
        out2_: Wrappers_Compile.Result
        out2_ = simple.types.boolean.internaldafny.impl.default__.SimpleBoolean(simple.types.boolean.internaldafny.impl.default__.DefaultSimpleBooleanConfig())
        d_76_valueOrError0_ = out2_
        if not(not((d_76_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/test/SimpleBooleanImplTest.dfy(14,19): " + _dafny.string_of(d_76_valueOrError0_))
        d_75_client_ = (d_76_valueOrError0_).Extract()
        SimpleBooleanImplTest_Compile.default__.TestGetBooleanFalse(d_75_client_)

    @staticmethod
    def TestGetBooleanTrue(client):
        d_77_ret_: simple.types.boolean.internaldafny.types.GetBooleanOutput
        d_78_valueOrError0_: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.types.boolean.internaldafny.types.GetBooleanOutput.default())()
        out3_: Wrappers_Compile.Result
        out3_ = (client).GetBoolean(simple.types.boolean.internaldafny.types.GetBooleanInput_GetBooleanInput(Wrappers_Compile.Option_Some(True)))
        d_78_valueOrError0_ = out3_
        if not(not((d_78_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/test/SimpleBooleanImplTest.dfy(23,16): " + _dafny.string_of(d_78_valueOrError0_))
        d_77_ret_ = (d_78_valueOrError0_).Extract()
        if not((((d_77_ret_).value).UnwrapOr(False)) == (True)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/test/SimpleBooleanImplTest.dfy(24,8): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        _dafny.print(_dafny.string_of(d_77_ret_))

    @staticmethod
    def TestGetBooleanFalse(client):
        d_79_ret_: simple.types.boolean.internaldafny.types.GetBooleanOutput
        d_80_valueOrError0_: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.types.boolean.internaldafny.types.GetBooleanOutput.default())()
        out4_: Wrappers_Compile.Result
        out4_ = (client).GetBoolean(simple.types.boolean.internaldafny.types.GetBooleanInput_GetBooleanInput(Wrappers_Compile.Option_Some(False)))
        d_80_valueOrError0_ = out4_
        if not(not((d_80_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/test/SimpleBooleanImplTest.dfy(33,16): " + _dafny.string_of(d_80_valueOrError0_))
        d_79_ret_ = (d_80_valueOrError0_).Extract()
        if not((((d_79_ret_).value).UnwrapOr(True)) == (False)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/test/SimpleBooleanImplTest.dfy(34,8): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        _dafny.print(_dafny.string_of(d_79_ret_))

