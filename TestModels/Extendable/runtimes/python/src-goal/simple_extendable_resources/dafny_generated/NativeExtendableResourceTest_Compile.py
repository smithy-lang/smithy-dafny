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

assert "NativeExtendableResourceTest_Compile" == __name__
NativeExtendableResourceTest_Compile = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "NativeExtendableResourceTest_Compile._default"
    @staticmethod
    def TestNativeResource():
        d_125_resource_: simple.extendable.resources.internaldafny.types.IExtendableResource
        out28_: simple.extendable.resources.internaldafny.types.IExtendableResource
        out28_ = simple.extendable.resources.internaldafny.nativeresourcefactory.default__.DafnyFactory()
        d_125_resource_ = out28_
        NativeExtendableResourceTest_Compile.default__.TestSomeGetResourceData(d_125_resource_)
        NativeExtendableResourceTest_Compile.default__.TestNoneGetResourceData(d_125_resource_)
        NativeExtendableResourceTest_Compile.default__.TestAlwaysModeledError(d_125_resource_)
        NativeExtendableResourceTest_Compile.default__.TestAlwaysMultipleErrors(d_125_resource_)
        NativeExtendableResourceTest_Compile.default__.TestAlwaysOpaqueError(d_125_resource_)
        NativeExtendableResourceTest_Compile.default__.TestNoneAlwaysOpaqueError(d_125_resource_)

    @staticmethod
    def TestSomeGetResourceData(resource):
        d_126_dataInput_: simple.extendable.resources.internaldafny.types.GetExtendableResourceDataInput
        d_126_dataInput_ = TestHelpers_Compile.default__.allSome()
        d_127_dataOutput_: simple.extendable.resources.internaldafny.types.GetExtendableResourceDataOutput
        d_128_valueOrError0_: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.extendable.resources.internaldafny.types.GetExtendableResourceDataOutput.default())()
        out29_: Wrappers_Compile.Result
        out29_ = (resource).GetExtendableResourceData(d_126_dataInput_)
        d_128_valueOrError0_ = out29_
        if not(not((d_128_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/NativeExtendableResourceTest.dfy(33,19): " + _dafny.string_of(d_128_valueOrError0_))
        d_127_dataOutput_ = (d_128_valueOrError0_).Extract()
        TestHelpers_Compile.default__.checkSome(d_127_dataOutput_, (ExtendableResource_Compile.default__).DEFAULT__RESOURCE__NAME)

    @staticmethod
    def TestNoneGetResourceData(resource):
        d_129_dataInput_: simple.extendable.resources.internaldafny.types.GetExtendableResourceDataInput
        d_129_dataInput_ = TestHelpers_Compile.default__.allNone()
        d_130_dataOutput_: simple.extendable.resources.internaldafny.types.GetExtendableResourceDataOutput
        d_131_valueOrError0_: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.extendable.resources.internaldafny.types.GetExtendableResourceDataOutput.default())()
        out30_: Wrappers_Compile.Result
        print("d_129_dataInput_")
        print(d_129_dataInput_)
        out30_ = (resource).GetExtendableResourceData(d_129_dataInput_)
        d_131_valueOrError0_ = out30_
        if not(not((d_131_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/NativeExtendableResourceTest.dfy(45,19): " + _dafny.string_of(d_131_valueOrError0_))
        d_130_dataOutput_ = (d_131_valueOrError0_).Extract()
        TestHelpers_Compile.default__.checkNone(d_130_dataOutput_, (ExtendableResource_Compile.default__).DEFAULT__RESOURCE__NAME)

    @staticmethod
    def TestAlwaysModeledError(resource):
        d_132_errorInput_: simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsInput
        d_132_errorInput_ = simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsInput_GetExtendableResourceErrorsInput(Wrappers_Compile.Option_Some(_dafny.Seq("Some")))
        d_133_errorOutput_: Wrappers_Compile.Result
        out31_: Wrappers_Compile.Result
        out31_ = (resource).AlwaysModeledError(d_132_errorInput_)
        d_133_errorOutput_ = out31_
        TestHelpers_Compile.default__.CheckModeledError(d_133_errorOutput_)

    @staticmethod
    def TestAlwaysMultipleErrors(resource):
        d_134_errorInput_: simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsInput
        d_134_errorInput_ = simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsInput_GetExtendableResourceErrorsInput(Wrappers_Compile.Option_Some(_dafny.Seq("Some")))
        d_135_errorOutput_: Wrappers_Compile.Result
        out32_: Wrappers_Compile.Result
        out32_ = (resource).AlwaysMultipleErrors(d_134_errorInput_)
        d_135_errorOutput_ = out32_
        TestHelpers_Compile.default__.CheckMultipleErrors(d_135_errorOutput_)

    @staticmethod
    def TestAlwaysOpaqueError(resource):
        d_136_errorInput_: simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsInput
        d_136_errorInput_ = simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsInput_GetExtendableResourceErrorsInput(Wrappers_Compile.Option_Some(_dafny.Seq("Some")))
        d_137_errorOutput_: Wrappers_Compile.Result
        out33_: Wrappers_Compile.Result
        out33_ = (resource).AlwaysOpaqueError(d_136_errorInput_)
        d_137_errorOutput_ = out33_
        if not((d_137_errorOutput_).is_Failure):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/NativeExtendableResourceTest.dfy(88,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        d_138_actualError_: simple.extendable.resources.internaldafny.types.Error
        d_138_actualError_ = (d_137_errorOutput_).error
        if not((d_138_actualError_).is_Opaque):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/NativeExtendableResourceTest.dfy(90,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))

    @staticmethod
    def TestNoneAlwaysOpaqueError(resource):
        d_139_errorInput_: simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsInput
        d_139_errorInput_ = simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsInput_GetExtendableResourceErrorsInput(Wrappers_Compile.Option_None())
        d_140_errorOutput_: Wrappers_Compile.Result
        out34_: Wrappers_Compile.Result
        out34_ = (resource).AlwaysOpaqueError(d_139_errorInput_)
        d_140_errorOutput_ = out34_
        TestHelpers_Compile.default__.CheckOpaqueError(d_140_errorOutput_)

