import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import SimpleBooleanImplTest_Compile
import Dafny.Simpletypes.Boolean.Wrapped
import WrappedSimpleTypesBooleanTest_Compile
import Extern

assert "module_" == __name__
module_ = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "_module._default"
    @staticmethod
    def Main(noArgsParameter__):
        d_12_success_: bool
        d_12_success_ = True
        _dafny.print(_dafny.string_of(_dafny.Seq("SimpleBooleanImplTest.GetBooleanTrue: "))
        )
        try:
            if True:
                SimpleBooleanImplTest_Compile.default__.GetBooleanTrue()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n"))
                    )
        except _dafny.HaltException as e:
            d_13_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	"))
                )
                _dafny.print(_dafny.string_of(d_13_haltMessage_)
                )
                _dafny.print(_dafny.string_of(_dafny.Seq("\n"))
                )
                d_12_success_ = False
        _dafny.print(_dafny.string_of(_dafny.Seq("SimpleBooleanImplTest.GetBooleanFalse: "))
        )
        try:
            if True:
                SimpleBooleanImplTest_Compile.default__.GetBooleanFalse()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n"))
                    )
        except _dafny.HaltException as e:
            d_14_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	"))
                )
                _dafny.print(_dafny.string_of(d_14_haltMessage_)
                )
                _dafny.print(_dafny.string_of(_dafny.Seq("\n"))
                )
                d_12_success_ = False
        _dafny.print(_dafny.string_of(_dafny.Seq("WrappedSimpleTypesBooleanTest.GetBooleanTrue: "))
        )
        try:
            if True:
                WrappedSimpleTypesBooleanTest_Compile.default__.GetBooleanTrue()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n"))
                    )
        except _dafny.HaltException as e:
            d_15_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	"))
                )
                _dafny.print(_dafny.string_of(d_15_haltMessage_)
                )
                _dafny.print(_dafny.string_of(_dafny.Seq("\n"))
                )
                d_12_success_ = False
        _dafny.print(_dafny.string_of(_dafny.Seq("WrappedSimpleTypesBooleanTest.GetBooleanFalse: "))
        )
        try:
            if True:
                WrappedSimpleTypesBooleanTest_Compile.default__.GetBooleanFalse()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n"))
                    )
        except _dafny.HaltException as e:
            d_16_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	"))
                )
                _dafny.print(_dafny.string_of(d_16_haltMessage_)
                )
                _dafny.print(_dafny.string_of(_dafny.Seq("\n"))
                )
                d_12_success_ = False
        if not(d_12_success_):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/SimpleTypes/SimpleBoolean/test/SimpleBooleanImplTest.dfy(7,18): " + _dafny.string_of(_dafny.Seq("Test failures occurred: see above.\n"))
            )

