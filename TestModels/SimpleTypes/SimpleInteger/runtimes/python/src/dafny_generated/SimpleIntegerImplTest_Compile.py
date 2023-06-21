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

assert "SimpleIntegerImplTest_Compile" == __name__
SimpleIntegerImplTest_Compile = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "SimpleIntegerImplTest_Compile._default"
    @staticmethod
    def GetInteger():
        d_74_client_: simple.types.integer.internaldafny.impl.SimpleIntegerClient
        d_75_valueOrError0_: Wrappers_Compile.Result = None
        out2_: Wrappers_Compile.Result
        out2_ = simple.types.integer.internaldafny.impl.default__.SimpleInteger(simple.types.integer.internaldafny.impl.default__.DefaultSimpleIntegerConfig())
        d_75_valueOrError0_ = out2_
        if not(not((d_75_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleInteger/test/SimpleIntegerImplTest.dfy(11,19): " + _dafny.string_of(d_75_valueOrError0_))
        d_74_client_ = (d_75_valueOrError0_).Extract()
        SimpleIntegerImplTest_Compile.default__.TestGetInteger(d_74_client_)
        SimpleIntegerImplTest_Compile.default__.TestGetIntegerKnownValue(d_74_client_)
        SimpleIntegerImplTest_Compile.default__.TestGetIntegerEdgeCases(d_74_client_)

    @staticmethod
    def TestGetInteger(client):
        d_76_ret_: simple.types.integer.internaldafny.types.GetIntegerOutput
        d_77_valueOrError0_: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.types.integer.internaldafny.types.GetIntegerOutput.default())()
        out3_: Wrappers_Compile.Result
        out3_ = (client).GetInteger(simple.types.integer.internaldafny.types.GetIntegerInput_GetIntegerInput(Wrappers_Compile.Option_Some(1)))
        d_77_valueOrError0_ = out3_
        if not(not((d_77_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleInteger/test/SimpleIntegerImplTest.dfy(22,16): " + _dafny.string_of(d_77_valueOrError0_))
        d_76_ret_ = (d_77_valueOrError0_).Extract()
        if not((((d_76_ret_).value).UnwrapOr(0)) == (1)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleInteger/test/SimpleIntegerImplTest.dfy(23,8): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        _dafny.print(_dafny.string_of(d_76_ret_))

    @staticmethod
    def TestGetIntegerKnownValue(client):
        d_78_ret_: simple.types.integer.internaldafny.types.GetIntegerOutput
        d_79_valueOrError0_: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.types.integer.internaldafny.types.GetIntegerOutput.default())()
        out4_: Wrappers_Compile.Result
        out4_ = (client).GetIntegerKnownValueTest(simple.types.integer.internaldafny.types.GetIntegerInput_GetIntegerInput(Wrappers_Compile.Option_Some(20)))
        d_79_valueOrError0_ = out4_
        if not(not((d_79_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleInteger/test/SimpleIntegerImplTest.dfy(32,16): " + _dafny.string_of(d_79_valueOrError0_))
        d_78_ret_ = (d_79_valueOrError0_).Extract()
        if not((((d_78_ret_).value).UnwrapOr(0)) == (20)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleInteger/test/SimpleIntegerImplTest.dfy(33,8): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        _dafny.print(_dafny.string_of(d_78_ret_))

    @staticmethod
    def TestGetIntegerEdgeCases(client):
        d_80_inputInteger_: _dafny.Seq
        d_80_inputInteger_ = _dafny.Seq([-1, 0, 1, ((StandardLibrary_mUInt_Compile.default__).INT32__MAX__LIMIT) - (1), (0) - (((StandardLibrary_mUInt_Compile.default__).INT32__MAX__LIMIT) - (1))])
        hi0_: int = len(d_80_inputInteger_)
        for d_81_i_ in range(0, hi0_):
            d_82_integerValue_: StandardLibrary_mUInt_Compile.int32
            d_82_integerValue_ = (d_80_inputInteger_)[d_81_i_]
            _dafny.print(_dafny.string_of(d_82_integerValue_))
            d_83_ret_: simple.types.integer.internaldafny.types.GetIntegerOutput
            d_84_valueOrError0_: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.types.integer.internaldafny.types.GetIntegerOutput.default())()
            out5_: Wrappers_Compile.Result
            out5_ = (client).GetInteger(simple.types.integer.internaldafny.types.GetIntegerInput_GetIntegerInput(Wrappers_Compile.Option_Some(d_82_integerValue_)))
            d_84_valueOrError0_ = out5_
            if not(not((d_84_valueOrError0_).IsFailure())):
                raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleInteger/test/SimpleIntegerImplTest.dfy(53,20): " + _dafny.string_of(d_84_valueOrError0_))
            d_83_ret_ = (d_84_valueOrError0_).Extract()
            if not((((d_83_ret_).value).UnwrapOr(0)) == (d_82_integerValue_)):
                raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleInteger/test/SimpleIntegerImplTest.dfy(54,12): " + _dafny.string_of(_dafny.Seq("expectation violation")))
            _dafny.print(_dafny.string_of(d_83_ret_))

