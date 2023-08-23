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

assert "SimpleDependenciesImplTest" == __name__
SimpleDependenciesImplTest = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def TestDependenciesWithDefaultConfig():
        d_34_client_: simple_dependencies_internaldafny.SimpleDependenciesClient
        d_35_valueOrError0_: Wrappers.Result = None
        out4_: Wrappers.Result
        out4_ = simple_dependencies_internaldafny.default__.SimpleDependencies(simple_dependencies_internaldafny.default__.DefaultSimpleDependenciesConfig())
        d_35_valueOrError0_ = out4_
        if not(not((d_35_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("test/SimpleDependenciesImplTest.dfy(18,19): " + _dafny.string_of(d_35_valueOrError0_))
        d_34_client_ = (d_35_valueOrError0_).Extract()
        SimpleDependenciesImplTest.default__.TestGetSimpleResource(d_34_client_)
        SimpleDependenciesImplTest.default__.TestUseSimpleResource(d_34_client_)
        SimpleDependenciesImplTest.default__.TestUseLocalExtendableResource(d_34_client_)
        SimpleDependenciesImplTest.default__.TestUseLocalConstraintsService(d_34_client_)
        SimpleDependenciesImplTest.default__.TestLocalExtendableResourceAlwaysModeledError(d_34_client_)
        SimpleDependenciesImplTest.default__.TestLocalExtendableResourceAlwaysMultipleErrors(d_34_client_)
        SimpleDependenciesImplTest.default__.TestLocalExtendableResourceAlwaysOpaqueError(d_34_client_)

    @staticmethod
    def TestDependenciesWithCustomConfig():
        d_36_extendableResourceReferenceToAssign_: ExtendableResource.ExtendableResource
        nw0_ = ExtendableResource.ExtendableResource()
        nw0_.ctor__()
        d_36_extendableResourceReferenceToAssign_ = nw0_
        d_37_simpleConstraintsServiceReferenceToAssign_: simple_constraints_internaldafny.SimpleConstraintsClient
        d_38_valueOrError0_: Wrappers.Result = None
        out5_: Wrappers.Result
        out5_ = simple_constraints_internaldafny.default__.SimpleConstraints(simple_constraints_internaldafny.default__.DefaultSimpleConstraintsConfig())
        d_38_valueOrError0_ = out5_
        if not(not((d_38_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("test/SimpleDependenciesImplTest.dfy(31,52): " + _dafny.string_of(d_38_valueOrError0_))
        d_37_simpleConstraintsServiceReferenceToAssign_ = (d_38_valueOrError0_).Extract()
        d_39_customConfig_: simple_dependencies_internaldafny_types.SimpleDependenciesConfig
        d_39_customConfig_ = simple_dependencies_internaldafny_types.SimpleDependenciesConfig_SimpleDependenciesConfig(Wrappers.Option_Some(simple_resources_internaldafny_types.SimpleResourcesConfig_SimpleResourcesConfig(_dafny.Seq("default"))), Wrappers.Option_Some(d_37_simpleConstraintsServiceReferenceToAssign_), Wrappers.Option_Some(d_36_extendableResourceReferenceToAssign_), Wrappers.Option_Some(_dafny.Seq("bw1and10")))
        d_40_client_: simple_dependencies_internaldafny.SimpleDependenciesClient
        d_41_valueOrError1_: Wrappers.Result = None
        out6_: Wrappers.Result
        out6_ = simple_dependencies_internaldafny.default__.SimpleDependencies(d_39_customConfig_)
        d_41_valueOrError1_ = out6_
        if not(not((d_41_valueOrError1_).IsFailure())):
            raise _dafny.HaltException("test/SimpleDependenciesImplTest.dfy(42,17): " + _dafny.string_of(d_41_valueOrError1_))
        d_40_client_ = (d_41_valueOrError1_).Extract()
        SimpleDependenciesImplTest.default__.TestGetSimpleResource(d_40_client_)
        SimpleDependenciesImplTest.default__.TestUseSimpleResource(d_40_client_)
        SimpleDependenciesImplTest.default__.TestUseLocalExtendableResource(d_40_client_)
        SimpleDependenciesImplTest.default__.TestUseLocalConstraintsService(d_40_client_)
        SimpleDependenciesImplTest.default__.TestLocalExtendableResourceAlwaysModeledError(d_40_client_)
        SimpleDependenciesImplTest.default__.TestLocalExtendableResourceAlwaysMultipleErrors(d_40_client_)
        SimpleDependenciesImplTest.default__.TestLocalExtendableResourceAlwaysOpaqueError(d_40_client_)

    @staticmethod
    def TestGetSimpleResource(client):
        d_42_input_: simple_resources_internaldafny_types.GetResourcesInput
        d_42_input_ = simple_resources_internaldafny_types.GetResourcesInput_GetResourcesInput(Wrappers.Option_Some(_dafny.Seq("anyInput")))
        d_43_res_: simple_resources_internaldafny_types.GetResourcesOutput
        d_44_valueOrError0_: Wrappers.Result = None
        out7_: Wrappers.Result
        out7_ = (client).GetSimpleResource(d_42_input_)
        d_44_valueOrError0_ = out7_
        if not(not((d_44_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("test/SimpleDependenciesImplTest.dfy(60,14): " + _dafny.string_of(d_44_valueOrError0_))
        d_43_res_ = (d_44_valueOrError0_).Extract()

    @staticmethod
    def TestUseSimpleResource(client):
        d_45_resourceDataInput_: simple_resources_internaldafny_types.GetResourceDataInput
        d_45_resourceDataInput_ = simple_resources_internaldafny_types.GetResourceDataInput_GetResourceDataInput(Wrappers.Option_Some(_dafny.Seq([0, 1])), Wrappers.Option_Some(True), Wrappers.Option_Some(_dafny.Seq("anyString")), Wrappers.Option_Some(123), Wrappers.Option_Some(123))
        d_46_getResourcesInput_: simple_resources_internaldafny_types.GetResourcesInput
        d_46_getResourcesInput_ = simple_resources_internaldafny_types.GetResourcesInput_GetResourcesInput(Wrappers.Option_Some(_dafny.Seq("anyInput")))
        d_47_getResourcesOutput_: simple_resources_internaldafny_types.GetResourcesOutput
        d_48_valueOrError0_: Wrappers.Result = None
        out8_: Wrappers.Result
        out8_ = (client).GetSimpleResource(d_46_getResourcesInput_)
        d_48_valueOrError0_ = out8_
        if not(not((d_48_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("test/SimpleDependenciesImplTest.dfy(79,29): " + _dafny.string_of(d_48_valueOrError0_))
        d_47_getResourcesOutput_ = (d_48_valueOrError0_).Extract()
        d_49_input_: simple_dependencies_internaldafny_types.UseSimpleResourceInput
        d_49_input_ = simple_dependencies_internaldafny_types.UseSimpleResourceInput_UseSimpleResourceInput((d_47_getResourcesOutput_).output, d_45_resourceDataInput_)
        d_50_res_: simple_resources_internaldafny_types.GetResourceDataOutput
        d_51_valueOrError1_: Wrappers.Result = Wrappers.Result_Success.default(simple_resources_internaldafny_types.GetResourceDataOutput.default())()
        out9_: Wrappers.Result
        out9_ = (client).UseSimpleResource(d_49_input_)
        d_51_valueOrError1_ = out9_
        if not(not((d_51_valueOrError1_).IsFailure())):
            raise _dafny.HaltException("test/SimpleDependenciesImplTest.dfy(86,14): " + _dafny.string_of(d_51_valueOrError1_))
        d_50_res_ = (d_51_valueOrError1_).Extract()

    @staticmethod
    def TestUseLocalConstraintsService(client):
        d_52_resourceDataInput_: simple_constraints_internaldafny_types.GetConstraintsInput
        out10_: simple_constraints_internaldafny_types.GetConstraintsInput
        out10_ = Helpers.default__.GetConstraintsInputTemplate(_dafny.Set({}))
        d_52_resourceDataInput_ = out10_
        d_53_res_: simple_constraints_internaldafny_types.GetConstraintsOutput
        d_54_valueOrError0_: Wrappers.Result = Wrappers.Result_Success.default(simple_constraints_internaldafny_types.GetConstraintsOutput.default())()
        out11_: Wrappers.Result
        out11_ = (client).UseLocalConstraintsService(d_52_resourceDataInput_)
        d_54_valueOrError0_ = out11_
        if not(not((d_54_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("test/SimpleDependenciesImplTest.dfy(97,14): " + _dafny.string_of(d_54_valueOrError0_))
        d_53_res_ = (d_54_valueOrError0_).Extract()
        if not(((d_53_res_).MyString).is_Some):
            raise _dafny.HaltException("test/SimpleDependenciesImplTest.dfy(98,6): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not((((d_53_res_).MyString).value) == (_dafny.Seq("bw1and10"))):
            raise _dafny.HaltException("test/SimpleDependenciesImplTest.dfy(99,6): " + _dafny.string_of(_dafny.Seq("expectation violation")))

    @staticmethod
    def TestUseLocalExtendableResource(client):
        print("using localextendable")
        d_55_resourceDataInput_: simple_extendable_resources_internaldafny_types.GetExtendableResourceDataInput
        d_55_resourceDataInput_ = simple_extendable_resources_internaldafny_types.GetExtendableResourceDataInput_GetExtendableResourceDataInput(Wrappers.Option_Some(_dafny.Seq([1])), Wrappers.Option_Some(True), Wrappers.Option_Some(_dafny.Seq("Some")), Wrappers.Option_Some(1), Wrappers.Option_Some(1))
        d_56_res_: simple_extendable_resources_internaldafny_types.UseExtendableResourceOutput
        d_57_valueOrError0_: Wrappers.Result = Wrappers.Result_Success.default(simple_extendable_resources_internaldafny_types.UseExtendableResourceOutput.default())()
        out12_: Wrappers.Result
        out12_ = (client).UseLocalExtendableResource(d_55_resourceDataInput_)
        d_57_valueOrError0_ = out12_
        if not(not((d_57_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("test/SimpleDependenciesImplTest.dfy(117,14): " + _dafny.string_of(d_57_valueOrError0_))
        d_56_res_ = (d_57_valueOrError0_).Extract()

    @staticmethod
    def TestLocalExtendableResourceAlwaysModeledError(client):
        d_58_errorInput_: simple_extendable_resources_internaldafny_types.GetExtendableResourceErrorsInput
        d_58_errorInput_ = simple_extendable_resources_internaldafny_types.GetExtendableResourceErrorsInput_GetExtendableResourceErrorsInput(Wrappers.Option_Some(_dafny.Seq("Some")))
        d_59_errorOutput_: Wrappers.Result
        out13_: Wrappers.Result
        out13_ = (client).LocalExtendableResourceAlwaysModeledError(d_58_errorInput_)
        d_59_errorOutput_ = out13_
        print("d_59_errorOutput_")
        print(d_59_errorOutput_)
        if not((d_59_errorOutput_).is_Failure):
            raise _dafny.HaltException("test/SimpleDependenciesImplTest.dfy(131,6): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not(((d_59_errorOutput_).error).is_SimpleExtendableResources):
            raise _dafny.HaltException("test/SimpleDependenciesImplTest.dfy(132,6): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not((((d_59_errorOutput_).error).SimpleExtendableResources).is_SimpleExtendableResourcesException):
            raise _dafny.HaltException("test/SimpleDependenciesImplTest.dfy(133,6): " + _dafny.string_of(_dafny.Seq("expectation violation")))

    @staticmethod
    def TestLocalExtendableResourceAlwaysMultipleErrors(client):
        d_60_errorInput_: simple_extendable_resources_internaldafny_types.GetExtendableResourceErrorsInput
        d_60_errorInput_ = simple_extendable_resources_internaldafny_types.GetExtendableResourceErrorsInput_GetExtendableResourceErrorsInput(Wrappers.Option_Some(_dafny.Seq("Some")))
        d_61_errorOutput_: Wrappers.Result
        out14_: Wrappers.Result
        out14_ = (client).LocalExtendableResourceAlwaysMultipleErrors(d_60_errorInput_)
        d_61_errorOutput_ = out14_
        print("d_61_errorOutput_")
        print(d_61_errorOutput_)
        if not((d_61_errorOutput_).is_Failure):
            raise _dafny.HaltException("test/SimpleDependenciesImplTest.dfy(147,6): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not(((d_61_errorOutput_).error).is_SimpleExtendableResources):
            raise _dafny.HaltException("test/SimpleDependenciesImplTest.dfy(148,6): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        zz = ((d_61_errorOutput_).error).SimpleExtendableResources
        print("zedzed")
        print(zz)
        print(zz.__dict__)
        print(zz.is_CollectionOfErrors)
        print(type(zz))
        if not((((d_61_errorOutput_).error).SimpleExtendableResources).is_CollectionOfErrors):
            raise _dafny.HaltException("test/SimpleDependenciesImplTest.dfy(149,6): " + _dafny.string_of(_dafny.Seq("expectation violation")))

    @staticmethod
    def TestLocalExtendableResourceAlwaysOpaqueError(client):
        d_62_errorInput_: simple_extendable_resources_internaldafny_types.GetExtendableResourceErrorsInput
        d_62_errorInput_ = simple_extendable_resources_internaldafny_types.GetExtendableResourceErrorsInput_GetExtendableResourceErrorsInput(Wrappers.Option_Some(_dafny.Seq("Some")))
        d_63_errorOutput_: Wrappers.Result
        out15_: Wrappers.Result
        out15_ = (client).LocalExtendableResourceAlwaysNativeError(d_62_errorInput_)
        d_63_errorOutput_ = out15_
        if not((d_63_errorOutput_).is_Failure):
            raise _dafny.HaltException("test/SimpleDependenciesImplTest.dfy(163,6): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not(((d_63_errorOutput_).error).is_SimpleExtendableResources):
            raise _dafny.HaltException("test/SimpleDependenciesImplTest.dfy(164,6): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not((((d_63_errorOutput_).error).SimpleExtendableResources).is_Opaque):
            raise _dafny.HaltException("test/SimpleDependenciesImplTest.dfy(165,6): " + _dafny.string_of(_dafny.Seq("expectation violation")))

