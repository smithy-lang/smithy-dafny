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
import SimpleBooleanImplTest_Compile
import simple.types.boolean.internaldafny.wrapped
import WrappedSimpleTypesBooleanTest_Compile

assert "module_" == __name__
module_ = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "_module._default"
    @staticmethod
    def Test____Main____(noArgsParameter__):
        d_85_success_: bool
        d_85_success_ = True
        _dafny.print(_dafny.string_of(_dafny.Seq("SimpleBooleanImplTest.GetBooleanTrue: ")))
        try:
            if True:
                SimpleBooleanImplTest_Compile.default__.GetBooleanTrue()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_86_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_86_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_85_success_ = False
        _dafny.print(_dafny.string_of(_dafny.Seq("SimpleBooleanImplTest.GetBooleanFalse: ")))
        try:
            if True:
                SimpleBooleanImplTest_Compile.default__.GetBooleanFalse()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_87_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_87_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_85_success_ = False
        _dafny.print(_dafny.string_of(_dafny.Seq("WrappedSimpleTypesBooleanTest.GetBooleanTrue: ")))
        try:
            if True:
                WrappedSimpleTypesBooleanTest_Compile.default__.GetBooleanTrue()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_88_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_88_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_85_success_ = False
        _dafny.print(_dafny.string_of(_dafny.Seq("WrappedSimpleTypesBooleanTest.GetBooleanFalse: ")))
        try:
            if True:
                WrappedSimpleTypesBooleanTest_Compile.default__.GetBooleanFalse()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_89_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_89_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_85_success_ = False
        if not(d_85_success_):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/test/SimpleBooleanImplTest.dfy(3,0): " + _dafny.string_of(_dafny.Seq("Test failures occurred: see above.\n")))

