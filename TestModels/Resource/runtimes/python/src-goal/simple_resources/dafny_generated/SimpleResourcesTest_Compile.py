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

assert "SimpleResourcesTest_Compile" == __name__
SimpleResourcesTest_Compile = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "SimpleResourcesTest_Compile._default"
    @staticmethod
    def TestNoneGetData(config, resource):
        d_77_input_: simple.resources.internaldafny.types.GetResourceDataInput
        d_77_input_ = Helpers_Compile.default__.allNone()
        d_78_result_: simple.resources.internaldafny.types.GetResourceDataOutput
        d_79_valueOrError0_: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.resources.internaldafny.types.GetResourceDataOutput.default())()
        out3_: Wrappers_Compile.Result
        print("resource")
        print(resource)
        out3_: Any
        try:
            out3_ = (resource).GetResourceData(d_77_input_)
            d_79_valueOrError0_ = out3_
        except Exception as e:
            print(e)
        print("d79")
        print(d_79_valueOrError0_)
        if not(not((d_79_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Resource/test/SimpleResourcesTest.dfy(22,15): " + _dafny.string_of(d_79_valueOrError0_))
        d_78_result_ = (d_79_valueOrError0_).Extract()
        Helpers_Compile.default__.checkMostNone((config).name, d_78_result_)

    @staticmethod
    def TestSomeGetData(config, resource):
        d_80_input_: simple.resources.internaldafny.types.GetResourceDataInput
        d_80_input_ = Helpers_Compile.default__.allSome()
        d_81_output_: simple.resources.internaldafny.types.GetResourceDataOutput
        d_82_valueOrError0_: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.resources.internaldafny.types.GetResourceDataOutput.default())()
        out4_: Wrappers_Compile.Result
        out4_ = (resource).GetResourceData(d_80_input_)
        d_82_valueOrError0_ = out4_
        if not(not((d_82_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Resource/test/SimpleResourcesTest.dfy(35,15): " + _dafny.string_of(d_82_valueOrError0_))
        d_81_output_ = (d_82_valueOrError0_).Extract()
        Helpers_Compile.default__.checkSome((config).name, d_81_output_)

    @staticmethod
    def TestGetResources(config, client):
        resource: simple.resources.internaldafny.types.ISimpleResource = None
        d_83_input_: simple.resources.internaldafny.types.GetResourcesInput
        d_83_input_ = simple.resources.internaldafny.types.GetResourcesInput_GetResourcesInput(Wrappers_Compile.Option_Some(_dafny.Seq("Test")))
        d_84_output_: simple.resources.internaldafny.types.GetResourcesOutput
        d_85_valueOrError0_: Wrappers_Compile.Result = None
        out5_: Wrappers_Compile.Result
        out5_ = (client).GetResources(d_83_input_)
        d_85_valueOrError0_ = out5_
        if not(not((d_85_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Resource/test/SimpleResourcesTest.dfy(55,15): " + _dafny.string_of(d_85_valueOrError0_))
        d_84_output_ = (d_85_valueOrError0_).Extract()
        resource = (d_84_output_).output
        return resource
        return resource

    @staticmethod
    def TestClient(config):
        d_86_client_: simple.resources.internaldafny.impl.SimpleResourcesClient
        d_87_valueOrError0_: Wrappers_Compile.Result = None
        out6_: Wrappers_Compile.Result
        out6_ = simple.resources.internaldafny.impl.default__.SimpleResources(config)
        d_87_valueOrError0_ = out6_
        if not(not((d_87_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Resource/test/SimpleResourcesTest.dfy(61,15): " + _dafny.string_of(d_87_valueOrError0_))
        d_86_client_ = (d_87_valueOrError0_).Extract()
        d_88_resource_: simple.resources.internaldafny.types.ISimpleResource
        out7_: simple.resources.internaldafny.types.ISimpleResource
        out7_ = SimpleResourcesTest_Compile.default__.TestGetResources(config, d_86_client_)
        d_88_resource_ = out7_
        SimpleResourcesTest_Compile.default__.TestNoneGetData(config, d_88_resource_)
        SimpleResourcesTest_Compile.default__.TestSomeGetData(config, d_88_resource_)

    @staticmethod
    def TestDefaultConfig():
        SimpleResourcesTest_Compile.default__.TestClient(simple.resources.internaldafny.impl.default__.DefaultSimpleResourcesConfig())

    @staticmethod
    def TestCustomConfig():
        SimpleResourcesTest_Compile.default__.TestClient(simple.resources.internaldafny.types.SimpleResourcesConfig_SimpleResourcesConfig(_dafny.Seq("Dafny")))

