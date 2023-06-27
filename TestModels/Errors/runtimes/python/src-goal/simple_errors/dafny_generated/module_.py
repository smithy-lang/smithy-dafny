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
import SimpleErrorsImplTest_Compile
import WrappedSimpleErrorsTest_Compile

assert "module_" == __name__
module_ = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "_module._default"
    @staticmethod
    def Test____Main____(noArgsParameter__):
        d_90_success_: bool
        d_90_success_ = True
        _dafny.print(_dafny.string_of(_dafny.Seq("SimpleErrorsImplTest.TestErrors: ")))
        try:
            if True:
                SimpleErrorsImplTest_Compile.default__.TestErrors()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_91_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_91_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_90_success_ = False
        _dafny.print(_dafny.string_of(_dafny.Seq("WrappedSimpleErrorsTest.GetErrors: ")))
        try:
            if True:
                WrappedSimpleErrorsTest_Compile.default__.GetErrors()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_92_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_92_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_90_success_ = False
        if not(d_90_success_):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Errors/test/WrappedSimpleErrorsTest.dfy(3,0): " + _dafny.string_of(_dafny.Seq("Test failures occurred: see above.\n")))

