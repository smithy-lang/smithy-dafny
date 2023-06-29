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
import simple.refinement.internaldafny.types
import SimpleRefinementImpl_Compile
import simple.refinement.internaldafny.impl
import simple.refinement.internaldafny.wrapped

assert "SimpleRefinementImplTest_Compile" == __name__
SimpleRefinementImplTest_Compile = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "SimpleRefinementImplTest_Compile._default"
    @staticmethod
    def Refinement():
        d_74_client_: simple.refinement.internaldafny.impl.SimpleRefinementClient
        d_75_valueOrError0_: Wrappers_Compile.Result = None
        out3_: Wrappers_Compile.Result
        out3_ = simple.refinement.internaldafny.impl.default__.SimpleRefinement(simple.refinement.internaldafny.impl.default__.DefaultSimpleRefinementConfig())
        d_75_valueOrError0_ = out3_
        if not(not((d_75_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Refinement/test/SimpleRefinementImplTest.dfy(10,19): " + _dafny.string_of(d_75_valueOrError0_))
        d_74_client_ = (d_75_valueOrError0_).Extract()
        SimpleRefinementImplTest_Compile.default__.TestGetRefinement(d_74_client_)
        SimpleRefinementImplTest_Compile.default__.TestOnlyInput(d_74_client_)
        SimpleRefinementImplTest_Compile.default__.TestOnlyOutput(d_74_client_)
        SimpleRefinementImplTest_Compile.default__.TestReadonlyOperation(d_74_client_)

    @staticmethod
    def TestGetRefinement(client):
        d_76_res_: simple.refinement.internaldafny.types.GetRefinementOutput
        d_77_valueOrError0_: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.refinement.internaldafny.types.GetRefinementOutput.default())()
        out4_: Wrappers_Compile.Result
        out4_ = (client).GetRefinement(simple.refinement.internaldafny.types.GetRefinementInput_GetRefinementInput(_dafny.Seq("GetRefinement"), Wrappers_Compile.Option_Some(_dafny.Seq("GetRefinementOptional"))))
        d_77_valueOrError0_ = out4_
        if not(not((d_77_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Refinement/test/SimpleRefinementImplTest.dfy(22,16): " + _dafny.string_of(d_77_valueOrError0_))
        d_76_res_ = (d_77_valueOrError0_).Extract()
        _dafny.print(_dafny.string_of(d_76_res_))
        print("d_76_res_")
        print(d_76_res_)
        if not(((d_76_res_).requiredString) == (_dafny.Seq("GetRefinement"))):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Refinement/test/SimpleRefinementImplTest.dfy(24,8): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not((((d_76_res_).optionalString).UnwrapOr(_dafny.Seq(""))) == (_dafny.Seq("GetRefinementOptional"))):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Refinement/test/SimpleRefinementImplTest.dfy(25,8): " + _dafny.string_of(_dafny.Seq("expectation violation")))

    @staticmethod
    def TestOnlyInput(client):
        d_78_res_: tuple
        d_79_valueOrError0_: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(_dafny.defaults.tuple())()
        out5_: Wrappers_Compile.Result
        out5_ = (client).OnlyInput(simple.refinement.internaldafny.types.OnlyInputInput_OnlyInputInput(Wrappers_Compile.Option_Some(_dafny.Seq("InputValue"))))
        d_79_valueOrError0_ = out5_
        if not(not((d_79_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Refinement/test/SimpleRefinementImplTest.dfy(33,16): " + _dafny.string_of(d_79_valueOrError0_))
        d_78_res_ = (d_79_valueOrError0_).Extract()
        _dafny.print(_dafny.string_of(d_78_res_))

    @staticmethod
    def TestOnlyOutput(client):
        d_80_res_: simple.refinement.internaldafny.types.OnlyOutputOutput
        d_81_valueOrError0_: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.refinement.internaldafny.types.OnlyOutputOutput.default())()
        out6_: Wrappers_Compile.Result
        out6_ = (client).OnlyOutput()
        d_81_valueOrError0_ = out6_
        if not(not((d_81_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Refinement/test/SimpleRefinementImplTest.dfy(42,16): " + _dafny.string_of(d_81_valueOrError0_))
        d_80_res_ = (d_81_valueOrError0_).Extract()
        _dafny.print(_dafny.string_of(d_80_res_))
        if not((((d_80_res_).value).UnwrapOr(_dafny.Seq(""))) == (_dafny.Seq("Hello World"))):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Refinement/test/SimpleRefinementImplTest.dfy(44,8): " + _dafny.string_of(_dafny.Seq("expectation violation")))

    @staticmethod
    def TestReadonlyOperation(client):
        d_82_res_: simple.refinement.internaldafny.types.ReadonlyOperationOutput
        d_83_valueOrError0_: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.refinement.internaldafny.types.ReadonlyOperationOutput.default())()
        d_83_valueOrError0_ = (client).ReadonlyOperation(simple.refinement.internaldafny.types.ReadonlyOperationInput_ReadonlyOperationInput(_dafny.Seq("Readonly"), Wrappers_Compile.Option_Some(_dafny.Seq("ReadonlyOptional"))))
        if not(not((d_83_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Refinement/test/SimpleRefinementImplTest.dfy(52,16): " + _dafny.string_of(d_83_valueOrError0_))
        d_82_res_ = (d_83_valueOrError0_).Extract()
        _dafny.print(_dafny.string_of(d_82_res_))
        if not(((d_82_res_).requiredString) == (_dafny.Seq("Readonly"))):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Refinement/test/SimpleRefinementImplTest.dfy(54,8): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not((((d_82_res_).optionalString).UnwrapOr(_dafny.Seq(""))) == (_dafny.Seq("ReadonlyOptional"))):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Refinement/test/SimpleRefinementImplTest.dfy(55,8): " + _dafny.string_of(_dafny.Seq("expectation violation")))

