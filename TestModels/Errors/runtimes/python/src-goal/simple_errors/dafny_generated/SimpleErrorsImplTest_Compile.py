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

assert "SimpleErrorsImplTest_Compile" == __name__
SimpleErrorsImplTest_Compile = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "SimpleErrorsImplTest_Compile._default"
    @staticmethod
    def TestErrors():
        d_76_client_: simple.errors.internaldafny.impl.SimpleErrorsClient
        d_77_valueOrError0_: Wrappers_Compile.Result = None
        out3_: Wrappers_Compile.Result
        out3_ = simple.errors.internaldafny.impl.default__.SimpleErrors(simple.errors.internaldafny.impl.default__.DefaultSimpleErrorsConfig())
        d_77_valueOrError0_ = out3_
        if not(not((d_77_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Errors/test/SimpleErrorsImplTest.dfy(11,19): " + _dafny.string_of(d_77_valueOrError0_))
        d_76_client_ = (d_77_valueOrError0_).Extract()
        SimpleErrorsImplTest_Compile.default__.TestAlwaysError(d_76_client_)
        SimpleErrorsImplTest_Compile.default__.TestAlwaysMultipleErrors(d_76_client_)
        SimpleErrorsImplTest_Compile.default__.TestAlwaysNativeError(d_76_client_)

    @staticmethod
    def TestAlwaysError(client):
        d_78_s_: _dafny.Seq
        d_78_s_ = _dafny.Seq("this is an error")
        d_79_convertedErrorInput_: simple.errors.internaldafny.types.GetErrorsInput
        d_79_convertedErrorInput_ = simple.errors.internaldafny.types.GetErrorsInput_GetErrorsInput(Wrappers_Compile.Option_Some(d_78_s_))
        d_80_ret_: Wrappers_Compile.Result
        out4_: Wrappers_Compile.Result
        out4_ = (client).AlwaysError(d_79_convertedErrorInput_)
        d_80_ret_ = out4_
        _dafny.print(_dafny.string_of(d_80_ret_))
        if not((d_80_ret_).is_Failure):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Errors/test/SimpleErrorsImplTest.dfy(28,6): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        print("checking results")
        print(d_80_ret_.error)
        print(simple.errors.internaldafny.types.Error_SimpleErrorsException(d_78_s_))
        print(d_80_ret_)
        print(d_78_s_)
        if not(((d_80_ret_).error) == (simple.errors.internaldafny.types.Error_SimpleErrorsException(d_78_s_))):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Errors/test/SimpleErrorsImplTest.dfy(29,6): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        print("passed TestAlwaysError!!!")

    @staticmethod
    def TestAlwaysMultipleErrors(client):
        d_81_s_: _dafny.Seq
        d_81_s_ = _dafny.Seq("this is in a collection of errors")
        d_82_convertedErrorInput_: simple.errors.internaldafny.types.GetErrorsInput
        d_82_convertedErrorInput_ = simple.errors.internaldafny.types.GetErrorsInput_GetErrorsInput(Wrappers_Compile.Option_Some(d_81_s_))
        d_83_ret_: Wrappers_Compile.Result
        out5_: Wrappers_Compile.Result
        out5_ = (client).AlwaysMultipleErrors(d_82_convertedErrorInput_)
        d_83_ret_ = out5_
        _dafny.print(_dafny.string_of(d_83_ret_))
        if not((d_83_ret_).is_Failure):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Errors/test/SimpleErrorsImplTest.dfy(43,6): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not(((d_83_ret_).error).is_CollectionOfErrors):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Errors/test/SimpleErrorsImplTest.dfy(44,6): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        d_84_expectedValue_: simple.errors.internaldafny.types.Error
        d_84_expectedValue_ = simple.errors.internaldafny.types.Error_CollectionOfErrors(_dafny.Seq([simple.errors.internaldafny.types.Error_SimpleErrorsException(d_81_s_)]), _dafny.Seq("Something"))
        if not(((d_83_ret_).error) == (d_84_expectedValue_)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Errors/test/SimpleErrorsImplTest.dfy(49,6): " + _dafny.string_of(_dafny.Seq("expectation violation")))

    @staticmethod
    def TestAlwaysNativeError(client):
        d_85_s_: _dafny.Seq
        d_85_s_ = _dafny.Seq("this will be a native/opaque error")
        d_86_convertedErrorInput_: simple.errors.internaldafny.types.GetErrorsInput
        d_86_convertedErrorInput_ = simple.errors.internaldafny.types.GetErrorsInput_GetErrorsInput(Wrappers_Compile.Option_Some(d_85_s_))
        d_87_ret_: Wrappers_Compile.Result
        out6_: Wrappers_Compile.Result
        out6_ = (client).AlwaysNativeError(d_86_convertedErrorInput_)
        d_87_ret_ = out6_
        if not((d_87_ret_).is_Failure):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Errors/test/SimpleErrorsImplTest.dfy(62,6): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not(((d_87_ret_).error).is_Opaque):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Errors/test/SimpleErrorsImplTest.dfy(63,6): " + _dafny.string_of(_dafny.Seq("expectation violation")))

