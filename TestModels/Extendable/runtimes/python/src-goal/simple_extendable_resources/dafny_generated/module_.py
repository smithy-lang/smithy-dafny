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
import simple.extendable.resources.internaldafny.types
import ExtendableResource_Compile
import TestHelpers_Compile
import SimpleExtendableResourcesOperations_Compile
import simple.extendable.resources.internaldafny.impl
import simple.extendable.resources.internaldafny.nativeresourcefactory
import SimpleExtendableResourcesTest_Compile
import simple.extendable.resources.internaldafny.wrapped
import NativeExtendableResourceTest_Compile
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
        d_147_success_: bool
        d_147_success_ = True
        _dafny.print(_dafny.string_of(_dafny.Seq("SimpleExtendableResourcesTest.TestClientDafnyResource: ")))
        try:
            if True:
                SimpleExtendableResourcesTest_Compile.default__.TestClientDafnyResource()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_148_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_148_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_147_success_ = False
        _dafny.print(_dafny.string_of(_dafny.Seq("SimpleExtendableResourcesTest.TestClientNativeResource: ")))
        try:
            if True:
                SimpleExtendableResourcesTest_Compile.default__.TestClientNativeResource()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_149_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_149_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_147_success_ = False
        _dafny.print(_dafny.string_of(_dafny.Seq("NativeExtendableResourceTest.TestNativeResource: ")))
        try:
            if True:
                NativeExtendableResourceTest_Compile.default__.TestNativeResource()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_150_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_150_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_147_success_ = False
        _dafny.print(_dafny.string_of(_dafny.Seq("WrappedTest.WrappedTestClientDafnyResource: ")))
        try:
            if True:
                WrappedTest_Compile.default__.WrappedTestClientDafnyResource()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_151_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_151_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_147_success_ = False
        _dafny.print(_dafny.string_of(_dafny.Seq("WrappedTest.WrappedTestClientNativeResource: ")))
        try:
            if True:
                WrappedTest_Compile.default__.WrappedTestClientNativeResource()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_152_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_152_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_147_success_ = False
        if not(d_147_success_):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/Helpers.dfy(4,0): " + _dafny.string_of(_dafny.Seq("Test failures occurred: see above.\n")))

