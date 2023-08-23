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
import simple_constraints_internaldafny_types
import simple_extendable_resources_internaldafny_types
import simple_resources_internaldafny_types
import simple_dependencies_internaldafny_types
import ExtendableResource
import SimpleResource
import SimpleResourcesOperations
import simple_resources_internaldafny
import SimpleDependenciesImpl
import SimpleConstraintsImpl
import simple_constraints_internaldafny
import simple_dependencies_internaldafny
import simple_dependencies_internaldafny_wrapped
import Helpers
import SimpleDependenciesImplTest
import WrappedSimpleDependenciesTest
import SimpleExtendableResourcesOperations
import simple_extendable_resources_internaldafny

assert "module_" == __name__
module_ = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def Test____Main____(noArgsParameter__):
        d_72_success_: bool
        d_72_success_ = True
        _dafny.print(_dafny.string_of(_dafny.Seq("SimpleDependenciesImplTest.TestDependenciesWithDefaultConfig: ")))
        try:
            if True:
                SimpleDependenciesImplTest.default__.TestDependenciesWithDefaultConfig()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_73_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_73_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_72_success_ = False
        _dafny.print(_dafny.string_of(_dafny.Seq("SimpleDependenciesImplTest.TestDependenciesWithCustomConfig: ")))
        try:
            if True:
                SimpleDependenciesImplTest.default__.TestDependenciesWithCustomConfig()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_74_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_74_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_72_success_ = False
        _dafny.print(_dafny.string_of(_dafny.Seq("WrappedSimpleDependenciesTest.TestDependenciesWithDefaultConfig: ")))
        try:
            if True:
                WrappedSimpleDependenciesTest.default__.TestDependenciesWithDefaultConfig()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_75_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_75_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_72_success_ = False
        _dafny.print(_dafny.string_of(_dafny.Seq("WrappedSimpleDependenciesTest.TestDependenciesWithCustomConfig: ")))
        try:
            if True:
                WrappedSimpleDependenciesTest.default__.TestDependenciesWithCustomConfig()
                if True:
                    _dafny.print(_dafny.string_of(_dafny.Seq("PASSED\n")))
        except _dafny.HaltException as e:
            d_76_haltMessage_ = e.message
            if True:
                _dafny.print(_dafny.string_of(_dafny.Seq("FAILED\n	")))
                _dafny.print(_dafny.string_of(d_76_haltMessage_))
                _dafny.print(_dafny.string_of(_dafny.Seq("\n")))
                d_72_success_ = False
        if not(d_72_success_):
            raise _dafny.HaltException("test/WrappedSimpleDependenciesTest.dfy(3,0): " + _dafny.string_of(_dafny.Seq("Test failures occurred: see above.\n")))

