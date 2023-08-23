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

assert "WrappedSimpleDependenciesTest" == __name__
WrappedSimpleDependenciesTest = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def TestDependenciesWithDefaultConfig():
        d_64_client_: simple_dependencies_internaldafny_types.ISimpleDependenciesClient
        d_65_valueOrError0_: Wrappers.Result = None
        out16_: Wrappers.Result
        out16_ = simple_dependencies_internaldafny_wrapped.default__.WrappedSimpleDependencies(simple_dependencies_internaldafny_wrapped.default__.WrappedDefaultSimpleDependenciesConfig())
        d_65_valueOrError0_ = out16_
        if not(not((d_65_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("test/WrappedSimpleDependenciesTest.dfy(16,19): " + _dafny.string_of(d_65_valueOrError0_))
        d_64_client_ = (d_65_valueOrError0_).Extract()
        SimpleDependenciesImplTest.default__.TestGetSimpleResource(d_64_client_)
        SimpleDependenciesImplTest.default__.TestUseSimpleResource(d_64_client_)
        SimpleDependenciesImplTest.default__.TestUseLocalConstraintsService(d_64_client_)
        SimpleDependenciesImplTest.default__.TestUseLocalExtendableResource(d_64_client_)
        SimpleDependenciesImplTest.default__.TestLocalExtendableResourceAlwaysModeledError(d_64_client_)
        SimpleDependenciesImplTest.default__.TestLocalExtendableResourceAlwaysMultipleErrors(d_64_client_)
        SimpleDependenciesImplTest.default__.TestLocalExtendableResourceAlwaysOpaqueError(d_64_client_)

    @staticmethod
    def TestDependenciesWithCustomConfig():
        d_66_extendableResourceReferenceToAssign_: ExtendableResource.ExtendableResource
        nw1_ = ExtendableResource.ExtendableResource()
        nw1_.ctor__()
        d_66_extendableResourceReferenceToAssign_ = nw1_
        d_67_simpleConstraintsServiceReferenceToAssign_: simple_constraints_internaldafny.SimpleConstraintsClient
        d_68_valueOrError0_: Wrappers.Result = None
        out17_: Wrappers.Result
        out17_ = simple_constraints_internaldafny.default__.SimpleConstraints(simple_constraints_internaldafny.default__.DefaultSimpleConstraintsConfig())
        d_68_valueOrError0_ = out17_
        if not(not((d_68_valueOrError0_).IsFailure())):
            raise _dafny.HaltException("test/WrappedSimpleDependenciesTest.dfy(29,54): " + _dafny.string_of(d_68_valueOrError0_))
        d_67_simpleConstraintsServiceReferenceToAssign_ = (d_68_valueOrError0_).Extract()
        d_69_customConfig_: simple_dependencies_internaldafny_types.SimpleDependenciesConfig
        d_69_customConfig_ = simple_dependencies_internaldafny_types.SimpleDependenciesConfig_SimpleDependenciesConfig(Wrappers.Option_Some(simple_resources_internaldafny_types.SimpleResourcesConfig_SimpleResourcesConfig(_dafny.Seq("default"))), Wrappers.Option_Some(d_67_simpleConstraintsServiceReferenceToAssign_), Wrappers.Option_Some(d_66_extendableResourceReferenceToAssign_), Wrappers.Option_Some(_dafny.Seq("bw1and10")))
        d_70_client_: simple_dependencies_internaldafny.SimpleDependenciesClient
        d_71_valueOrError1_: Wrappers.Result = None
        out18_: Wrappers.Result
        out18_ = simple_dependencies_internaldafny.default__.SimpleDependencies(d_69_customConfig_)
        d_71_valueOrError1_ = out18_
        if not(not((d_71_valueOrError1_).IsFailure())):
            raise _dafny.HaltException("test/WrappedSimpleDependenciesTest.dfy(40,19): " + _dafny.string_of(d_71_valueOrError1_))
        d_70_client_ = (d_71_valueOrError1_).Extract()
        SimpleDependenciesImplTest.default__.TestGetSimpleResource(d_70_client_)
        SimpleDependenciesImplTest.default__.TestUseSimpleResource(d_70_client_)
        SimpleDependenciesImplTest.default__.TestUseLocalConstraintsService(d_70_client_)
        SimpleDependenciesImplTest.default__.TestUseLocalExtendableResource(d_70_client_)
        SimpleDependenciesImplTest.default__.TestLocalExtendableResourceAlwaysModeledError(d_70_client_)
        SimpleDependenciesImplTest.default__.TestLocalExtendableResourceAlwaysMultipleErrors(d_70_client_)
        SimpleDependenciesImplTest.default__.TestLocalExtendableResourceAlwaysOpaqueError(d_70_client_)

