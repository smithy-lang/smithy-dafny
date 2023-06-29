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
import SimpleRefinementImplTest_Compile
import WrappedSimpleRefinementTest_Compile

assert "module_" == __name__
module_ = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "_module._default"
    @staticmethod
    def Test____Main____(noArgsParameter__):
        d_86_success_: bool
        d_86_success_ = True
        _dafny.print(_dafny.string_of(_dafny.Seq("SimpleRefinementImplTest.Refinement: ")))
        try:
            if True:
                SimpleRefinementImplTest_Compile.default__.Refinement()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_87_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_87_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_86_success_ = False
        _dafny.print(_dafny.string_of(_dafny.Seq("WrappedSimpleRefinementTest.Refinement: ")))
        try:
            if True:
                WrappedSimpleRefinementTest_Compile.default__.Refinement()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_88_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_88_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_86_success_ = False
        if not(d_86_success_):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Refinement/test/WrappedSimpleRefinementImplTest.dfy(3,0): " + _dafny.string_of(_dafny.Seq("Test failures occurred: see above.\n")))

