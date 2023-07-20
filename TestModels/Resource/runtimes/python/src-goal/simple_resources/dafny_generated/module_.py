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
import simple.resources.internaldafny.types
import Helpers_Compile
import SimpleResource_Compile
import SimpleResourcesOperations_Compile
import simple.resources.internaldafny.impl
import SimpleResourcesTest_Compile
import simple.resources.internaldafny.wrapped
import WrappedTest_Compile

assert "module_" == __name__
module_ = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "_module._default"
    @staticmethod
    def Test____Main____(noArgsParameter__):
        d_92_success_: bool
        d_92_success_ = True
        _dafny.print(_dafny.string_of(_dafny.Seq("SimpleResourcesTest.TestDefaultConfig: ")))
        try:
            if True:
                SimpleResourcesTest_Compile.default__.TestDefaultConfig()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_93_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_93_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_92_success_ = False
        _dafny.print(_dafny.string_of(_dafny.Seq("SimpleResourcesTest.TestCustomConfig: ")))
        try:
            if True:
                SimpleResourcesTest_Compile.default__.TestCustomConfig()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_94_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_94_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_92_success_ = False
        _dafny.print(_dafny.string_of(_dafny.Seq("WrappedTest.WrappedTestDefaultConfig: ")))
        try:
            if True:
                WrappedTest_Compile.default__.WrappedTestDefaultConfig()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_95_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_95_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_92_success_ = False
        _dafny.print(_dafny.string_of(_dafny.Seq("WrappedTest.WrappedTestCustomConfig: ")))
        try:
            if True:
                WrappedTest_Compile.default__.WrappedTestCustomConfig()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_96_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_96_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_92_success_ = False
        if not(d_92_success_):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Resource/test/Helpers.dfy(4,0): " + _dafny.string_of(_dafny.Seq("Test failures occurred: see above.\n")))

