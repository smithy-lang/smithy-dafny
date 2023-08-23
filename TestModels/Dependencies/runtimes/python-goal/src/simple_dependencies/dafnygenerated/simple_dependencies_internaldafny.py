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

assert "simple_dependencies_internaldafny" == __name__
simple_dependencies_internaldafny = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def DefaultSimpleDependenciesConfig():
        return simple_dependencies_internaldafny_types.SimpleDependenciesConfig_SimpleDependenciesConfig(Wrappers.Option_Some(simple_resources_internaldafny_types.SimpleResourcesConfig_SimpleResourcesConfig(_dafny.Seq("default"))), Wrappers.Option_None(), Wrappers.Option_None(), Wrappers.Option_Some(_dafny.Seq("bw1and10")))

    @staticmethod
    def SimpleDependencies(config):
        res: Wrappers.Result = None
        if not(((config).simpleResourcesConfig).is_Some):
            raise _dafny.HaltException("src/Index.dfy(30,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not(((config).specialString).is_Some):
            raise _dafny.HaltException("src/Index.dfy(31,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        d_26_extendableResourceReferenceToAssign_: simple_extendable_resources_internaldafny_types.IExtendableResource = None
        if ((config).extendableResourceReference).is_Some:
            d_26_extendableResourceReferenceToAssign_ = ((config).extendableResourceReference).value
        elif True:
            nw1_ = ExtendableResource.ExtendableResource()
            nw1_.ctor__()
            d_26_extendableResourceReferenceToAssign_ = nw1_
        d_27_simpleConstraintsServiceReferenceToAssign_: simple_constraints_internaldafny_types.ISimpleConstraintsClient = None
        if ((config).simpleConstraintsServiceReference).is_Some:
            d_27_simpleConstraintsServiceReferenceToAssign_ = ((config).simpleConstraintsServiceReference).value
        elif True:
            d_28_newSimpleConstraintsServiceReference_: Wrappers.Result
            out5_: Wrappers.Result
            out5_ = simple_constraints_internaldafny.default__.SimpleConstraints(simple_constraints_internaldafny.default__.DefaultSimpleConstraintsConfig())
            d_28_newSimpleConstraintsServiceReference_ = out5_
            if not((d_28_newSimpleConstraintsServiceReference_).is_Success):
                raise _dafny.HaltException("src/Index.dfy(49,6): " + _dafny.string_of(_dafny.Seq("expectation violation")))
            d_27_simpleConstraintsServiceReferenceToAssign_ = (d_28_newSimpleConstraintsServiceReference_).value
        d_29_configToAssign_: SimpleDependenciesImpl.Config
        d_29_configToAssign_ = SimpleDependenciesImpl.Config_Config(((config).simpleResourcesConfig).value, d_27_simpleConstraintsServiceReferenceToAssign_, d_26_extendableResourceReferenceToAssign_, ((config).specialString).value)
        d_30_client_: simple_dependencies_internaldafny.SimpleDependenciesClient
        nw2_ = simple_dependencies_internaldafny.SimpleDependenciesClient()
        nw2_.ctor__(d_29_configToAssign_)
        d_30_client_ = nw2_
        res = Wrappers.Result_Success(d_30_client_)
        return res
        return res


class SimpleDependenciesClient(simple_dependencies_internaldafny_types.ISimpleDependenciesClient):
    def  __init__(self):
        self._config: SimpleDependenciesImpl.Config = None
        pass

    def __dafnystr__(self) -> str:
        return "SimpleDependencies.SimpleDependenciesClient"
    def ctor__(self, config):
        (self)._config = config

    def GetSimpleResource(self, input):
        output: Wrappers.Result = None
        out6_: Wrappers.Result
        out6_ = SimpleDependenciesImpl.default__.GetSimpleResource((self).config, input)
        output = out6_
        return output

    def UseSimpleResource(self, input):
        output: Wrappers.Result = Wrappers.Result.default(simple_resources_internaldafny_types.GetResourceDataOutput.default())()
        out7_: Wrappers.Result
        out7_ = SimpleDependenciesImpl.default__.UseSimpleResource((self).config, input)
        output = out7_
        return output

    def UseLocalConstraintsService(self, input):
        output: Wrappers.Result = Wrappers.Result.default(simple_constraints_internaldafny_types.GetConstraintsOutput.default())()
        out8_: Wrappers.Result
        out8_ = SimpleDependenciesImpl.default__.UseLocalConstraintsService((self).config, input)
        output = out8_
        return output

    def UseLocalExtendableResource(self, input):
        output: Wrappers.Result = Wrappers.Result.default(simple_extendable_resources_internaldafny_types.UseExtendableResourceOutput.default())()
        out9_: Wrappers.Result
        out9_ = SimpleDependenciesImpl.default__.UseLocalExtendableResource((self).config, input)
        output = out9_
        return output

    def LocalExtendableResourceAlwaysModeledError(self, input):
        output: Wrappers.Result = Wrappers.Result.default(simple_extendable_resources_internaldafny_types.GetExtendableResourceErrorsOutput.default())()
        out10_: Wrappers.Result
        out10_ = SimpleDependenciesImpl.default__.LocalExtendableResourceAlwaysModeledError((self).config, input)
        output = out10_
        return output

    def LocalExtendableResourceAlwaysMultipleErrors(self, input):
        output: Wrappers.Result = Wrappers.Result.default(simple_extendable_resources_internaldafny_types.GetExtendableResourceErrorsOutput.default())()
        out11_: Wrappers.Result
        out11_ = SimpleDependenciesImpl.default__.LocalExtendableResourceAlwaysMultipleErrors((self).config, input)
        output = out11_
        return output

    def LocalExtendableResourceAlwaysNativeError(self, input):
        output: Wrappers.Result = Wrappers.Result.default(simple_extendable_resources_internaldafny_types.GetExtendableResourceErrorsOutput.default())()
        out12_: Wrappers.Result
        out12_ = SimpleDependenciesImpl.default__.LocalExtendableResourceAlwaysNativeError((self).config, input)
        output = out12_
        return output

    @property
    def config(self):
        return self._config
