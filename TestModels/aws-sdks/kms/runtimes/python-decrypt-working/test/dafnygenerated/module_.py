import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import Wrappers
import StandardLibrary_mUInt
import StandardLibrary
import UTF8
import software_amazon_cryptography_services_kms_internaldafny_types
import software_amazon_cryptography_services_kms_internaldafny
import TestComAmazonawsKms

assert "module_" == __name__
module_ = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Test____Main____(noArgsParameter__):
        d_24_success_: bool
        d_24_success_ = True
        _dafny.print(_dafny.string_of(_dafny.Seq("TestComAmazonawsKms.BasicDecryptTests: ")))
        try:
            if True:
                TestComAmazonawsKms.default__.BasicDecryptTests()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_25_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_25_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_24_success_ = False
        _dafny.print(_dafny.string_of(_dafny.Seq("TestComAmazonawsKms.BasicGenerateTests: ")))
        try:
            if True:
                TestComAmazonawsKms.default__.BasicGenerateTests()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_26_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_26_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_24_success_ = False
        _dafny.print(_dafny.string_of(_dafny.Seq("TestComAmazonawsKms.BasicEncryptTests: ")))
        try:
            if True:
                TestComAmazonawsKms.default__.BasicEncryptTests()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_27_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_27_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_24_success_ = False
        _dafny.print(_dafny.string_of(_dafny.Seq("TestComAmazonawsKms.RegionMatchTest: ")))
        try:
            if True:
                TestComAmazonawsKms.default__.RegionMatchTest()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_28_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_28_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_24_success_ = False
        if not(d_24_success_):
            raise _dafny.HaltException("test/TestComAmazonawsKms.dfy(4,0): " + _dafny.string_of(_dafny.Seq("Test failures occurred: see above.\n")))

