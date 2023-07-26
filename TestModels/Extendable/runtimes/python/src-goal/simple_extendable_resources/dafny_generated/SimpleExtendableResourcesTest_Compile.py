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

assert "SimpleExtendableResourcesTest_Compile" == __name__
SimpleExtendableResourcesTest_Compile = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "SimpleExtendableResourcesTest_Compile._default"
    @staticmethod
    def TestClientDafnyResource():
        d_96_client_: simple.extendable.resources.internaldafny.impl.SimpleExtendableResourcesClient
        d_97_valueOrError0_: Wrappers_Compile.Result = None
        out17_: Wrappers_Compile.Result
        out17_ = simple.extendable.resources.internaldafny.impl.default__.SimpleExtendableResources(simple.extendable.resources.internaldafny.impl.default__.DefaultSimpleExtendableResourcesConfig())
        d_97_valueOrError0_ = out17_
        if not(not((d_97_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/SimpleExtendableResourcesTest.dfy(21,15): " + _dafny.string_of(d_97_valueOrError0_))
        d_96_client_ = (d_97_valueOrError0_).Extract()
        d_98_resource_: simple.extendable.resources.internaldafny.types.IExtendableResource
        out18_: simple.extendable.resources.internaldafny.types.IExtendableResource
        out18_ = SimpleExtendableResourcesTest_Compile.default__.TestCreateExtendableResource(d_96_client_, (SimpleExtendableResourcesTest_Compile.default__).TEST__RESOURCE__NAME)
        d_98_resource_ = out18_
        def iife2_(_is_2):
            return isinstance(_is_2, ExtendableResource_Compile.ExtendableResource)
        if not(iife2_(d_98_resource_)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/SimpleExtendableResourcesTest.dfy(26,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        SimpleExtendableResourcesTest_Compile.default__.TestNoneUseExtendableResource(d_96_client_, d_98_resource_, (SimpleExtendableResourcesTest_Compile.default__).TEST__RESOURCE__NAME)
        SimpleExtendableResourcesTest_Compile.default__.TestSomeUseExtendableResource(d_96_client_, d_98_resource_, (SimpleExtendableResourcesTest_Compile.default__).TEST__RESOURCE__NAME)
        SimpleExtendableResourcesTest_Compile.default__.TestUseAlwaysModeledError(d_96_client_, d_98_resource_)
        SimpleExtendableResourcesTest_Compile.default__.TestUseAlwaysMultipleErrors(d_96_client_, d_98_resource_)
        SimpleExtendableResourcesTest_Compile.default__.TestDafnyUseAlwaysOpaqueError(d_96_client_, d_98_resource_)

    @staticmethod
    def TestClientNativeResource():
        d_99_client_: simple.extendable.resources.internaldafny.impl.SimpleExtendableResourcesClient
        d_100_valueOrError0_: Wrappers_Compile.Result = None
        out19_: Wrappers_Compile.Result
        out19_ = simple.extendable.resources.internaldafny.impl.default__.SimpleExtendableResources(simple.extendable.resources.internaldafny.impl.default__.DefaultSimpleExtendableResourcesConfig())
        d_100_valueOrError0_ = out19_
        if not(not((d_100_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/SimpleExtendableResourcesTest.dfy(38,15): " + _dafny.string_of(d_100_valueOrError0_))
        d_99_client_ = (d_100_valueOrError0_).Extract()
        d_101_resource_: simple.extendable.resources.internaldafny.types.IExtendableResource
        out20_: simple.extendable.resources.internaldafny.types.IExtendableResource
        out20_ = simple.extendable.resources.internaldafny.nativeresourcefactory.default__.DafnyFactory()
        d_101_resource_ = out20_
        def iife3_(_is_3):
            return isinstance(_is_3, ExtendableResource_Compile.ExtendableResource)
        if not(not(iife3_(d_101_resource_))):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/SimpleExtendableResourcesTest.dfy(41,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        SimpleExtendableResourcesTest_Compile.default__.TestNoneUseExtendableResource(d_99_client_, d_101_resource_, (ExtendableResource_Compile.default__).DEFAULT__RESOURCE__NAME)
        SimpleExtendableResourcesTest_Compile.default__.TestSomeUseExtendableResource(d_99_client_, d_101_resource_, (ExtendableResource_Compile.default__).DEFAULT__RESOURCE__NAME)
        SimpleExtendableResourcesTest_Compile.default__.TestUseAlwaysModeledError(d_99_client_, d_101_resource_)
        SimpleExtendableResourcesTest_Compile.default__.TestUseAlwaysMultipleErrors(d_99_client_, d_101_resource_)
        SimpleExtendableResourcesTest_Compile.default__.TestUseAlwaysOpaqueError(d_99_client_, d_101_resource_)

    @staticmethod
    def TestCreateExtendableResource(client, name):
        resource: simple.extendable.resources.internaldafny.types.IExtendableResource = None
        d_102_createInput_: simple.extendable.resources.internaldafny.types.CreateExtendableResourceInput
        d_102_createInput_ = simple.extendable.resources.internaldafny.types.CreateExtendableResourceInput_CreateExtendableResourceInput(name)
        d_103_createOutput_: simple.extendable.resources.internaldafny.types.CreateExtendableResourceOutput
        d_104_valueOrError0_: Wrappers_Compile.Result = None
        out21_: Wrappers_Compile.Result
        out21_ = (client).CreateExtendableResource(d_102_createInput_)
        d_104_valueOrError0_ = out21_
        if not(not((d_104_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/SimpleExtendableResourcesTest.dfy(67,21): " + _dafny.string_of(d_104_valueOrError0_))
        d_103_createOutput_ = (d_104_valueOrError0_).Extract()
        resource = (d_103_createOutput_).resource
        return resource

    @staticmethod
    def TestNoneUseExtendableResource(client, resource, name):
        d_105_dataInput_: simple.extendable.resources.internaldafny.types.GetExtendableResourceDataInput
        d_105_dataInput_ = TestHelpers_Compile.default__.allNone()
        d_106_useInput_: simple.extendable.resources.internaldafny.types.UseExtendableResourceInput
        d_106_useInput_ = simple.extendable.resources.internaldafny.types.UseExtendableResourceInput_UseExtendableResourceInput(resource, d_105_dataInput_)
        d_107_useOutput_: simple.extendable.resources.internaldafny.types.UseExtendableResourceOutput
        d_108_valueOrError0_: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.extendable.resources.internaldafny.types.UseExtendableResourceOutput.default())()
        out22_: Wrappers_Compile.Result
        print("d_106_useInput_")
        print(d_106_useInput_)
        out22_ = (client).UseExtendableResource(d_106_useInput_)
        print("out22_")
        print(out22_)
        d_108_valueOrError0_ = out22_
        if not(not((d_108_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/SimpleExtendableResourcesTest.dfy(86,18): " + _dafny.string_of(d_108_valueOrError0_))
        d_107_useOutput_ = (d_108_valueOrError0_).Extract()
        TestHelpers_Compile.default__.checkNone((d_107_useOutput_).output, name)

    @staticmethod
    def TestSomeUseExtendableResource(client, resource, name):
        d_109_dataInput_: simple.extendable.resources.internaldafny.types.GetExtendableResourceDataInput
        d_109_dataInput_ = TestHelpers_Compile.default__.allSome()
        d_110_useInput_: simple.extendable.resources.internaldafny.types.UseExtendableResourceInput
        d_110_useInput_ = simple.extendable.resources.internaldafny.types.UseExtendableResourceInput_UseExtendableResourceInput(resource, d_109_dataInput_)
        d_111_useOutput_: simple.extendable.resources.internaldafny.types.UseExtendableResourceOutput
        d_112_valueOrError0_: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.extendable.resources.internaldafny.types.UseExtendableResourceOutput.default())()
        out23_: Wrappers_Compile.Result
        out23_ = (client).UseExtendableResource(d_110_useInput_)
        d_112_valueOrError0_ = out23_
        if not(not((d_112_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/SimpleExtendableResourcesTest.dfy(105,18): " + _dafny.string_of(d_112_valueOrError0_))
        d_111_useOutput_ = (d_112_valueOrError0_).Extract()
        TestHelpers_Compile.default__.checkSome((d_111_useOutput_).output, name)

    @staticmethod
    def TestUseAlwaysModeledError(client, resource):
        d_113_errorInput_: simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsInput
        d_113_errorInput_ = simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsInput_GetExtendableResourceErrorsInput(Wrappers_Compile.Option_Some(_dafny.Seq("Some")))
        d_114_useInput_: simple.extendable.resources.internaldafny.types.UseExtendableResourceErrorsInput
        d_114_useInput_ = simple.extendable.resources.internaldafny.types.UseExtendableResourceErrorsInput_UseExtendableResourceErrorsInput(resource, d_113_errorInput_)
        d_115_useOutput_: Wrappers_Compile.Result
        out24_: Wrappers_Compile.Result
        out24_ = (client).UseExtendableResourceAlwaysModeledError(d_114_useInput_)
        d_115_useOutput_ = out24_
        TestHelpers_Compile.default__.CheckModeledError(d_115_useOutput_)

    @staticmethod
    def TestUseAlwaysMultipleErrors(client, resource):
        d_116_errorInput_: simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsInput
        d_116_errorInput_ = simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsInput_GetExtendableResourceErrorsInput(Wrappers_Compile.Option_Some(_dafny.Seq("Some")))
        d_117_useInput_: simple.extendable.resources.internaldafny.types.UseExtendableResourceErrorsInput
        d_117_useInput_ = simple.extendable.resources.internaldafny.types.UseExtendableResourceErrorsInput_UseExtendableResourceErrorsInput(resource, d_116_errorInput_)
        d_118_useOutput_: Wrappers_Compile.Result
        out25_: Wrappers_Compile.Result
        out25_ = (client).UseExtendableResourceAlwaysMultipleErrors(d_117_useInput_)
        d_118_useOutput_ = out25_
        TestHelpers_Compile.default__.CheckMultipleErrors(d_118_useOutput_)

    @staticmethod
    def TestUseAlwaysOpaqueError(client, resource):
        d_119_errorInput_: simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsInput
        d_119_errorInput_ = simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsInput_GetExtendableResourceErrorsInput(Wrappers_Compile.Option_Some(_dafny.Seq("Some")))
        d_120_useInput_: simple.extendable.resources.internaldafny.types.UseExtendableResourceErrorsInput
        d_120_useInput_ = simple.extendable.resources.internaldafny.types.UseExtendableResourceErrorsInput_UseExtendableResourceErrorsInput(resource, d_119_errorInput_)
        d_121_useOutput_: Wrappers_Compile.Result
        out26_: Wrappers_Compile.Result
        out26_ = (client).UseExtendableResourceAlwaysOpaqueError(d_120_useInput_)
        d_121_useOutput_ = out26_
        TestHelpers_Compile.default__.CheckOpaqueError(d_121_useOutput_)

    @staticmethod
    def TestDafnyUseAlwaysOpaqueError(client, resource):
        d_122_errorInput_: simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsInput
        d_122_errorInput_ = simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsInput_GetExtendableResourceErrorsInput(Wrappers_Compile.Option_Some(_dafny.Seq("Some")))
        d_123_useInput_: simple.extendable.resources.internaldafny.types.UseExtendableResourceErrorsInput
        d_123_useInput_ = simple.extendable.resources.internaldafny.types.UseExtendableResourceErrorsInput_UseExtendableResourceErrorsInput(resource, d_122_errorInput_)
        d_124_useOutput_: Wrappers_Compile.Result
        out27_: Wrappers_Compile.Result
        out27_ = (client).UseExtendableResourceAlwaysOpaqueError(d_123_useInput_)
        d_124_useOutput_ = out27_
        TestHelpers_Compile.default__.CheckDafnyOpaqueError(d_124_useOutput_)

    @_dafny.classproperty
    def TEST__RESOURCE__NAME(instance):
        return _dafny.Seq("Dafny-Test")
