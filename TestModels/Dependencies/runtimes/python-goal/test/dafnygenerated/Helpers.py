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

assert "Helpers" == __name__
Helpers = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def GetConstraintsInputTemplate(overrideToInvalidInput):
        output: simple_constraints_internaldafny_types.GetConstraintsInput = simple_constraints_internaldafny_types.GetConstraintsInput_GetConstraintsInput.default()()
        d_0_overrideMyString_: bool
        d_0_overrideMyString_ = (_dafny.Seq("myString")) in (overrideToInvalidInput)
        d_1_myString_: _dafny.Seq = None
        if d_0_overrideMyString_:
            out0_: _dafny.Seq
            out0_ = Helpers.default__.InvalidMyStringInput()
            d_1_myString_ = out0_
        elif True:
            d_1_myString_ = _dafny.Seq("bw1and10")
        d_2_overrideNonEmptyString_: bool
        d_2_overrideNonEmptyString_ = (_dafny.Seq("nonEmptyString")) in (overrideToInvalidInput)
        d_3_nonEmptyString_: _dafny.Seq = None
        if d_2_overrideNonEmptyString_:
            out1_: _dafny.Seq
            out1_ = Helpers.default__.InvalidNonEmptyStringInput()
            d_3_nonEmptyString_ = out1_
        elif True:
            d_3_nonEmptyString_ = _dafny.Seq("atleast1")
        d_4_overrideStringLessThanOrEqualToTen_: bool
        d_4_overrideStringLessThanOrEqualToTen_ = (_dafny.Seq("overrideStringLessThanOrEqualToTen")) in (overrideToInvalidInput)
        d_5_stringLessThanOrEqualToTen_: _dafny.Seq = None
        if d_4_overrideStringLessThanOrEqualToTen_:
            out2_: _dafny.Seq
            out2_ = Helpers.default__.InvalidStringLessThanOrEqualToTen()
            d_5_stringLessThanOrEqualToTen_ = out2_
        elif True:
            d_5_stringLessThanOrEqualToTen_ = _dafny.Seq("leq10")
        d_6_overrideMyBlob_: bool
        d_6_overrideMyBlob_ = (_dafny.Seq("myBlob")) in (overrideToInvalidInput)
        d_7_myBlob_: _dafny.Seq = None
        if d_6_overrideMyBlob_:
            out3_: _dafny.Seq
            out3_ = Helpers.default__.InvalidMyBlob()
            d_7_myBlob_ = out3_
        elif True:
            d_7_myBlob_ = _dafny.Seq([0, 1, 0, 1])
        d_8_nonEmptyBlob_: _dafny.Seq
        d_8_nonEmptyBlob_ = _dafny.Seq([0, 1, 0, 1])
        d_9_BlobLessThanOrEqualToTen_: _dafny.Seq
        d_9_BlobLessThanOrEqualToTen_ = _dafny.Seq([0, 1, 0, 1])
        d_10_myList_: _dafny.Seq
        d_10_myList_ = _dafny.Seq([_dafny.Seq("00"), _dafny.Seq("11")])
        d_11_nonEmptyList_: _dafny.Seq
        d_11_nonEmptyList_ = _dafny.Seq([_dafny.Seq("00"), _dafny.Seq("11")])
        d_12_listLessThanOrEqualToTen_: _dafny.Seq
        d_12_listLessThanOrEqualToTen_ = _dafny.Seq([_dafny.Seq("00"), _dafny.Seq("11")])
        d_13_myMap_: _dafny.Map
        d_13_myMap_ = _dafny.Map({_dafny.Seq("0"): _dafny.Seq("1"), _dafny.Seq("2"): _dafny.Seq("3")})
        d_14_nonEmptyMap_: _dafny.Map
        d_14_nonEmptyMap_ = _dafny.Map({_dafny.Seq("0"): _dafny.Seq("1"), _dafny.Seq("2"): _dafny.Seq("3")})
        d_15_mapLessThanOrEqualToTen_: _dafny.Map
        d_15_mapLessThanOrEqualToTen_ = _dafny.Map({_dafny.Seq("0"): _dafny.Seq("1"), _dafny.Seq("2"): _dafny.Seq("3")})
        d_16_alphabetic_: _dafny.Seq
        d_16_alphabetic_ = _dafny.Seq("alphabetic")
        d_17_oneToTen_: StandardLibrary_mUInt.int32
        d_17_oneToTen_ = 3
        d_18_greaterThanOne_: StandardLibrary_mUInt.int32
        d_18_greaterThanOne_ = 2
        d_19_lessThanTen_: StandardLibrary_mUInt.int32
        d_19_lessThanTen_ = 3
        d_20_myUniqueList_: _dafny.Seq
        d_20_myUniqueList_ = _dafny.Seq([_dafny.Seq("one"), _dafny.Seq("two")])
        d_21_myComplexUniqueList_: _dafny.Seq
        d_21_myComplexUniqueList_ = _dafny.Seq([simple_constraints_internaldafny_types.ComplexListElement_ComplexListElement(Wrappers.Option_Some(_dafny.Seq("one")), Wrappers.Option_Some(_dafny.Seq([1, 1]))), simple_constraints_internaldafny_types.ComplexListElement_ComplexListElement(Wrappers.Option_Some(_dafny.Seq("two")), Wrappers.Option_Some(_dafny.Seq([2, 2])))])
        d_22_input_: simple_constraints_internaldafny_types.GetConstraintsInput
        d_22_input_ = simple_constraints_internaldafny_types.GetConstraintsInput_GetConstraintsInput(Wrappers.Option_Some(d_1_myString_), Wrappers.Option_Some(d_3_nonEmptyString_), Wrappers.Option_Some(d_5_stringLessThanOrEqualToTen_), Wrappers.Option_Some(d_7_myBlob_), Wrappers.Option_Some(d_8_nonEmptyBlob_), Wrappers.Option_Some(d_9_BlobLessThanOrEqualToTen_), Wrappers.Option_Some(d_10_myList_), Wrappers.Option_Some(d_11_nonEmptyList_), Wrappers.Option_Some(d_12_listLessThanOrEqualToTen_), Wrappers.Option_Some(d_13_myMap_), Wrappers.Option_Some(d_14_nonEmptyMap_), Wrappers.Option_Some(d_15_mapLessThanOrEqualToTen_), Wrappers.Option_Some(d_16_alphabetic_), Wrappers.Option_Some(d_17_oneToTen_), Wrappers.Option_Some(d_18_greaterThanOne_), Wrappers.Option_Some(d_19_lessThanTen_), Wrappers.Option_Some(d_20_myUniqueList_), Wrappers.Option_Some(d_21_myComplexUniqueList_), Wrappers.Option_Some((Helpers.default__).PROVIDER__ID), Wrappers.Option_Some(_dafny.Seq([(Helpers.default__).PROVIDER__ID, (Helpers.default__).PROVIDER__ID])))
        output = d_22_input_
        return output
        return output

    @staticmethod
    def InvalidLessThanTenInput():
        invalid: StandardLibrary_mUInt.int32 = None
        d_23_invalidLessThanTenInput_: StandardLibrary_mUInt.int32
        d_23_invalidLessThanTenInput_ = 12
        d_24_invalidLessThanTen_: StandardLibrary_mUInt.int32
        d_24_invalidLessThanTen_ = d_23_invalidLessThanTenInput_
        invalid = d_24_invalidLessThanTen_
        return invalid
        return invalid

    @staticmethod
    def InvalidMyStringInput():
        invalid: _dafny.Seq = None
        d_25_invalidMyStringInput_: _dafny.Seq
        d_25_invalidMyStringInput_ = _dafny.Seq("thisislongerthan10characters")
        d_26_invalidMyString_: _dafny.Seq
        d_26_invalidMyString_ = d_25_invalidMyStringInput_
        invalid = d_26_invalidMyString_
        return invalid
        return invalid

    @staticmethod
    def InvalidNonEmptyStringInput():
        invalid: _dafny.Seq = None
        d_27_invalidNonEmptyStringInput_: _dafny.Seq
        d_27_invalidNonEmptyStringInput_ = _dafny.Seq("")
        d_28_invalidNonEmptyString_: _dafny.Seq
        d_28_invalidNonEmptyString_ = d_27_invalidNonEmptyStringInput_
        invalid = d_28_invalidNonEmptyString_
        return invalid
        return invalid

    @staticmethod
    def InvalidStringLessThanOrEqualToTen():
        invalid: _dafny.Seq = None
        d_29_invalidStringLessThanOrEqualToTenInput_: _dafny.Seq
        d_29_invalidStringLessThanOrEqualToTenInput_ = _dafny.Seq("")
        d_30_invalidStringLessThanOrEqualToTen_: _dafny.Seq
        d_30_invalidStringLessThanOrEqualToTen_ = d_29_invalidStringLessThanOrEqualToTenInput_
        invalid = d_30_invalidStringLessThanOrEqualToTen_
        return invalid
        return invalid

    @staticmethod
    def InvalidMyBlob():
        invalid: _dafny.Seq = None
        d_31_invalidMyBlobInput_: _dafny.Seq
        d_31_invalidMyBlobInput_ = _dafny.Seq([])
        d_32_invalidMyBlob_: _dafny.Seq
        d_32_invalidMyBlob_ = d_31_invalidMyBlobInput_
        invalid = d_32_invalidMyBlob_
        return invalid
        return invalid

    @_dafny.classproperty
    def PROVIDER__ID(instance):
        d_33_s_ = _dafny.Seq([97, 119, 115, 45, 107, 109, 115])
        return d_33_s_
