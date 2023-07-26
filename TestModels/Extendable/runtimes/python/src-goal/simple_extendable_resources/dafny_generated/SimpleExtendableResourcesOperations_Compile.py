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

assert "SimpleExtendableResourcesOperations_Compile" == __name__
SimpleExtendableResourcesOperations_Compile = sys.modules[__name__]

class Config:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [Config_Config()]
    @classmethod
    def default(cls, ):
        return lambda: Config_Config()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_Config(self) -> bool:
        return isinstance(self, SimpleExtendableResourcesOperations_Compile.Config_Config)

class Config_Config(Config, NamedTuple('Config', [])):
    def __dafnystr__(self) -> str:
        return f'SimpleExtendableResourcesOperations_Compile.Config.Config'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, SimpleExtendableResourcesOperations_Compile.Config_Config)
    def __hash__(self) -> int:
        return super().__hash__()


class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "SimpleExtendableResourcesOperations_Compile._default"
    @staticmethod
    def ValidInternalConfig_q(config):
        return True

    @staticmethod
    def CreateExtendableResource(config, input):
        output: Wrappers_Compile.Result = None
        d_79_resource_: ExtendableResource_Compile.ExtendableResource
        nw2_ = ExtendableResource_Compile.ExtendableResource()
        nw2_.OfName((input).name)
        d_79_resource_ = nw2_
        d_80_result_: simple.extendable.resources.internaldafny.types.CreateExtendableResourceOutput
        d_80_result_ = simple.extendable.resources.internaldafny.types.CreateExtendableResourceOutput_CreateExtendableResourceOutput(d_79_resource_)
        output = Wrappers_Compile.Result_Success(d_80_result_)
        return output
        return output

    @staticmethod
    def UseExtendableResource(config, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.extendable.resources.internaldafny.types.UseExtendableResourceOutput.default())()
        d_81_resource_: simple.extendable.resources.internaldafny.types.IExtendableResource
        d_81_resource_ = (input).resource
        print("d_81_resource_")
        print(d_81_resource_)
        d_82_data_: simple.extendable.resources.internaldafny.types.GetExtendableResourceDataOutput
        d_83_valueOrError0_: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.extendable.resources.internaldafny.types.GetExtendableResourceDataOutput.default())()
        out8_: Wrappers_Compile.Result
        out8_ = (d_81_resource_).GetExtendableResourceData((input).input)
        d_83_valueOrError0_ = out8_
        if (d_83_valueOrError0_).IsFailure():
            output = (d_83_valueOrError0_).PropagateFailure()
            return output
        d_82_data_ = (d_83_valueOrError0_).Extract()
        print("d_82_data_")
        print(d_82_data_)
        d_84_result_: simple.extendable.resources.internaldafny.types.UseExtendableResourceOutput
        d_84_result_ = simple.extendable.resources.internaldafny.types.UseExtendableResourceOutput_UseExtendableResourceOutput(d_82_data_)
        output = Wrappers_Compile.Result_Success(d_84_result_)
        return output
        return output

    @staticmethod
    def UseExtendableResourceAlwaysModeledError(config, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsOutput.default())()
        d_85_resource_: simple.extendable.resources.internaldafny.types.IExtendableResource
        d_85_resource_ = (input).resource
        d_86_result_: simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsOutput
        d_87_valueOrError0_: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsOutput.default())()
        out9_: Wrappers_Compile.Result
        out9_ = (d_85_resource_).AlwaysModeledError((input).input)
        d_87_valueOrError0_ = out9_
        if (d_87_valueOrError0_).IsFailure():
            output = (d_87_valueOrError0_).PropagateFailure()
            return output
        d_86_result_ = (d_87_valueOrError0_).Extract()
        output = Wrappers_Compile.Result_Success(d_86_result_)
        return output
        return output

    @staticmethod
    def UseExtendableResourceAlwaysMultipleErrors(config, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsOutput.default())()
        d_88_resource_: simple.extendable.resources.internaldafny.types.IExtendableResource
        d_88_resource_ = (input).resource
        d_89_result_: simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsOutput
        d_90_valueOrError0_: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsOutput.default())()
        out10_: Wrappers_Compile.Result
        out10_ = (d_88_resource_).AlwaysMultipleErrors((input).input)
        d_90_valueOrError0_ = out10_
        if (d_90_valueOrError0_).IsFailure():
            output = (d_90_valueOrError0_).PropagateFailure()
            return output
        d_89_result_ = (d_90_valueOrError0_).Extract()
        output = Wrappers_Compile.Result_Success(d_89_result_)
        return output
        return output

    @staticmethod
    def UseExtendableResourceAlwaysOpaqueError(config, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsOutput.default())()
        d_91_resource_: simple.extendable.resources.internaldafny.types.IExtendableResource
        d_91_resource_ = (input).resource
        d_92_result_: simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsOutput
        d_93_valueOrError0_: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsOutput.default())()
        out11_: Wrappers_Compile.Result
        out11_ = (d_91_resource_).AlwaysOpaqueError((input).input)
        d_93_valueOrError0_ = out11_
        if (d_93_valueOrError0_).IsFailure():
            output = (d_93_valueOrError0_).PropagateFailure()
            return output
        d_92_result_ = (d_93_valueOrError0_).Extract()
        output = Wrappers_Compile.Result_Success(d_92_result_)
        return output
        return output

