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
import SimpleIntegerImplTest_Compile
import WrappedSimpleTypesIntegerTest_Compile

assert "module_" == __name__
module_ = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "_module._default"
    @staticmethod
    def Test____Main____(noArgsParameter__):
        d_87_success_: bool
        d_87_success_ = True
        _dafny.print(_dafny.string_of(_dafny.Seq("SimpleIntegerImplTest.GetInteger: ")))
        try:
            if True:
                SimpleIntegerImplTest_Compile.default__.GetInteger()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_88_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_88_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_87_success_ = False
        _dafny.print(_dafny.string_of(_dafny.Seq("WrappedSimpleTypesIntegerTest.GetInteger: ")))
        try:
            if True:
                WrappedSimpleTypesIntegerTest_Compile.default__.GetInteger()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_89_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_89_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_87_success_ = False
        if not(d_87_success_):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleInteger/test/WrappedSimpleIntegerTest.dfy(3,0): " + _dafny.string_of(_dafny.Seq("Test failures occurred: see above.\n")))

