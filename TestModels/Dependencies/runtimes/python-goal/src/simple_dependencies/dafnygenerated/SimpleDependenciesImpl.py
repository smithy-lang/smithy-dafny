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

assert "SimpleDependenciesImpl" == __name__
SimpleDependenciesImpl = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def GetSimpleResource(config, input):
        output: Wrappers.Result = None
        if not(((input).value).is_Some):
            raise _dafny.HaltException("src/SimpleDependenciesImpl.dfy(84,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        d_0_simpleResourcesConfig_: simple_resources_internaldafny_types.SimpleResourcesConfig
        d_0_simpleResourcesConfig_ = (config).simpleResourcesConfig
        d_1_client_: simple_resources_internaldafny.SimpleResourcesClient
        d_2_valueOrError0_: Wrappers.Result = None
        out0_: Wrappers.Result
        out0_ = simple_resources_internaldafny.default__.SimpleResources(d_0_simpleResourcesConfig_)
        d_2_valueOrError0_ = out0_
        if not(not((d_2_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("src/SimpleDependenciesImpl.dfy(88,54): " + _dafny.string_of(d_2_valueOrError0_))
        d_1_client_ = (d_2_valueOrError0_).Extract()
        d_3_res_: simple_resources_internaldafny_types.GetResourcesOutput
        d_4_valueOrError1_: Wrappers.Result = None
        out1_: Wrappers.Result
        out1_ = (d_1_client_).GetResources(input)
        d_4_valueOrError1_ = out1_
        if not(not((d_4_valueOrError1_).IsFailure())):
            raise _dafny.HaltException("src/SimpleDependenciesImpl.dfy(92,12): " + _dafny.string_of(d_4_valueOrError1_))
        d_3_res_ = (d_4_valueOrError1_).Extract()
        output = Wrappers.Result_Success(d_3_res_)
        return output
        return output

    @staticmethod
    def UseSimpleResource(config, input):
        output: Wrappers.Result = Wrappers.Result.default(simple_resources_internaldafny_types.GetResourceDataOutput.default())()
        d_5_reference_: simple_resources_internaldafny_types.ISimpleResource
        d_5_reference_ = (input).value
        d_6_getResourceDataInput_: simple_resources_internaldafny_types.GetResourceDataInput
        d_6_getResourceDataInput_ = (input).input
        d_7_res_: simple_resources_internaldafny_types.GetResourceDataOutput
        d_8_valueOrError0_: Wrappers.Result = Wrappers.Result.default(simple_resources_internaldafny_types.GetResourceDataOutput.default())()
        out2_: Wrappers.Result
        out2_ = (d_5_reference_).GetResourceData(d_6_getResourceDataInput_)
        d_8_valueOrError0_ = out2_
        if not(not((d_8_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("src/SimpleDependenciesImpl.dfy(102,56): " + _dafny.string_of(d_8_valueOrError0_))
        d_7_res_ = (d_8_valueOrError0_).Extract()
        output = Wrappers.Result_Success(d_7_res_)
        return output
        return output

    @staticmethod
    def UseLocalConstraintsService(config, input):
        print("using")
        output: Wrappers.Result = Wrappers.Result.default(simple_constraints_internaldafny_types.GetConstraintsOutput.default())()
        d_9_simpleConstraintsService_: simple_constraints_internaldafny_types.ISimpleConstraintsClient
        print("1")
        d_9_simpleConstraintsService_ = (config).simpleConstraintsServiceReference
        d_10_res_: simple_constraints_internaldafny_types.GetConstraintsOutput
        d_11_valueOrError0_: Wrappers.Result = Wrappers.Result.default(simple_constraints_internaldafny_types.GetConstraintsOutput.default())()
        out3_: Wrappers.Result
        print("2")
        try:
            out3_ = (d_9_simpleConstraintsService_).GetConstraints(input)
        except Exception as e:
            print(type(d_9_simpleConstraintsService_))
            print(e)
        d_11_valueOrError0_ = out3_
        print("3")
        if not(not((d_11_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("src/SimpleDependenciesImpl.dfy(110,12): " + _dafny.string_of(d_11_valueOrError0_))
        d_10_res_ = (d_11_valueOrError0_).Extract()
        output = Wrappers.Result_Success(d_10_res_)
        print("output")
        print(output)
        return output
        return output

    @staticmethod
    def UseLocalExtendableResource(config, input):
        try:
            output: Wrappers.Result = Wrappers.Result.default(simple_extendable_resources_internaldafny_types.UseExtendableResourceOutput.default())()
            d_12_reference_: simple_extendable_resources_internaldafny_types.IExtendableResource
            print(config)
            d_12_reference_ = (config).extendableResourceReference
            d_13_callInput_: simple_extendable_resources_internaldafny_types.UseExtendableResourceInput
            d_13_callInput_ = simple_extendable_resources_internaldafny_types.UseExtendableResourceInput_UseExtendableResourceInput(d_12_reference_, input)
            d_14_res_: simple_extendable_resources_internaldafny_types.GetExtendableResourceDataOutput
            d_15_valueOrError0_: Wrappers.Result = Wrappers.Result.default(simple_extendable_resources_internaldafny_types.GetExtendableResourceDataOutput.default())()
            out4_: Wrappers.Result
            out4_ = (d_12_reference_).GetExtendableResourceData(input)
            d_15_valueOrError0_ = out4_
            if not(not((d_15_valueOrError0_).IsFailure())):
                raise _dafny.HaltException("src/SimpleDependenciesImpl.dfy(123,12): " + _dafny.string_of(d_15_valueOrError0_))
            d_14_res_ = (d_15_valueOrError0_).Extract()
            d_16_toReturn_: simple_extendable_resources_internaldafny_types.UseExtendableResourceOutput
            d_16_toReturn_ = simple_extendable_resources_internaldafny_types.UseExtendableResourceOutput_UseExtendableResourceOutput(d_14_res_)
            output = Wrappers.Result_Success(d_16_toReturn_)
            return output
            return output
        except Exception as e:
            print(e)

    @staticmethod
    def LocalExtendableResourceAlwaysModeledError(config, input):
        output: Wrappers.Result = Wrappers.Result.default(simple_extendable_resources_internaldafny_types.GetExtendableResourceErrorsOutput.default())()
        d_17_extendableResourceError_: simple_extendable_resources_internaldafny_types.Error
        d_17_extendableResourceError_ = simple_extendable_resources_internaldafny_types.Error_SimpleExtendableResourcesException(_dafny.Seq("Hard Coded Exception in src/dafny"))
        d_18_dependenciesError_: simple_dependencies_internaldafny_types.Error
        d_18_dependenciesError_ = simple_dependencies_internaldafny_types.Error_SimpleExtendableResources(d_17_extendableResourceError_)
        output = Wrappers.Result_Failure(d_18_dependenciesError_)
        print("d_18_dependenciesError_")
        print(d_18_dependenciesError_)
        print(output)
        return output
        return output

    @staticmethod
    def LocalExtendableResourceAlwaysMultipleErrors(config, input):
        print("always multiple")
        print(input)
        output: Wrappers.Result = Wrappers.Result.default(simple_extendable_resources_internaldafny_types.GetExtendableResourceErrorsOutput.default())()
        d_19_nestedExtendableResourceError_: simple_extendable_resources_internaldafny_types.Error
        d_19_nestedExtendableResourceError_ = simple_extendable_resources_internaldafny_types.Error_SimpleExtendableResourcesException(_dafny.Seq("Hard Coded Modeled Exception in Collection"))
        d_20_nestedExtendableResourceError2_: simple_extendable_resources_internaldafny_types.Error
        d_20_nestedExtendableResourceError2_ = simple_extendable_resources_internaldafny_types.Error_SimpleExtendableResourcesException(_dafny.Seq("msg no 2"))
        d_21_collectionOfExtendableResourceErrors_: simple_extendable_resources_internaldafny_types.Error
        d_21_collectionOfExtendableResourceErrors_ = simple_extendable_resources_internaldafny_types.Error_CollectionOfErrors(_dafny.Seq([d_19_nestedExtendableResourceError_, d_20_nestedExtendableResourceError2_]), _dafny.Seq("2 Somethings"))
        d_22_dependenciesError_: simple_dependencies_internaldafny_types.Error
        d_22_dependenciesError_ = simple_dependencies_internaldafny_types.Error_SimpleExtendableResources(d_21_collectionOfExtendableResourceErrors_)
        output = Wrappers.Result_Failure(d_22_dependenciesError_)
        print("always multiple end")
        print(output)
        return output
        return output

    @staticmethod
    def LocalExtendableResourceAlwaysNativeError(config, input):
        output: Wrappers.Result = Wrappers.Result.default(simple_extendable_resources_internaldafny_types.GetExtendableResourceErrorsOutput.default())()
        d_23_obj_: object
        nw0_ = ExtendableResource.OpaqueMessage()
        nw0_.ctor__()
        d_23_obj_ = nw0_
        d_24_extendableResourceError_: simple_extendable_resources_internaldafny_types.Error
        d_24_extendableResourceError_ = simple_extendable_resources_internaldafny_types.Error_Opaque(d_23_obj_)
        d_25_dependenciesError_: simple_dependencies_internaldafny_types.Error
        d_25_dependenciesError_ = simple_dependencies_internaldafny_types.Error_SimpleExtendableResources(d_24_extendableResourceError_)
        output = Wrappers.Result_Failure(d_25_dependenciesError_)
        return output
        return output


class Config:
    @classmethod
    def default(cls, ):
        return lambda: Config_Config(simple_resources_internaldafny_types.SimpleResourcesConfig.default()(), None, None, _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Config(self) -> bool:
        return isinstance(self, SimpleDependenciesImpl.Config_Config)

class Config_Config(Config, NamedTuple('Config', [('simpleResourcesConfig', Any), ('simpleConstraintsServiceReference', Any), ('extendableResourceReference', Any), ('specialString', Any)])):
    def __dafnystr__(self) -> str:
        return f'SimpleDependenciesImpl.Config.Config({_dafny.string_of(self.simpleResourcesConfig)}, {_dafny.string_of(self.simpleConstraintsServiceReference)}, {_dafny.string_of(self.extendableResourceReference)}, {_dafny.string_of(self.specialString)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, SimpleDependenciesImpl.Config_Config) and self.simpleResourcesConfig == __o.simpleResourcesConfig and self.simpleConstraintsServiceReference == __o.simpleConstraintsServiceReference and self.extendableResourceReference == __o.extendableResourceReference and self.specialString == __o.specialString
    def __hash__(self) -> int:
        return super().__hash__()

