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

assert "simple_dependencies_internaldafny_types" == __name__
simple_dependencies_internaldafny_types = sys.modules[__name__]


class DafnyCallEvent:
    @classmethod
    def default(cls, default_I, default_O):
        return lambda: DafnyCallEvent_DafnyCallEvent(default_I(), default_O())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_DafnyCallEvent(self) -> bool:
        return isinstance(self, simple_dependencies_internaldafny_types.DafnyCallEvent_DafnyCallEvent)

class DafnyCallEvent_DafnyCallEvent(DafnyCallEvent, NamedTuple('DafnyCallEvent', [('input', Any), ('output', Any)])):
    def __dafnystr__(self) -> str:
        return f'SimpleDependenciesTypes.DafnyCallEvent.DafnyCallEvent({_dafny.string_of(self.input)}, {_dafny.string_of(self.output)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, simple_dependencies_internaldafny_types.DafnyCallEvent_DafnyCallEvent) and self.input == __o.input and self.output == __o.output
    def __hash__(self) -> int:
        return super().__hash__()


class ISimpleDependenciesClientCallHistory:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "SimpleDependenciesTypes.ISimpleDependenciesClientCallHistory"

class ISimpleDependenciesClient:
    pass
    def GetSimpleResource(self, input):
        pass

    def UseSimpleResource(self, input):
        pass

    def UseLocalConstraintsService(self, input):
        pass

    def UseLocalExtendableResource(self, input):
        pass

    def LocalExtendableResourceAlwaysModeledError(self, input):
        pass

    def LocalExtendableResourceAlwaysMultipleErrors(self, input):
        pass

    def LocalExtendableResourceAlwaysNativeError(self, input):
        pass


class SimpleDependenciesConfig:
    @classmethod
    def default(cls, ):
        return lambda: SimpleDependenciesConfig_SimpleDependenciesConfig(Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()(), Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_SimpleDependenciesConfig(self) -> bool:
        return isinstance(self, simple_dependencies_internaldafny_types.SimpleDependenciesConfig_SimpleDependenciesConfig)

class SimpleDependenciesConfig_SimpleDependenciesConfig(SimpleDependenciesConfig, NamedTuple('SimpleDependenciesConfig', [('simpleResourcesConfig', Any), ('simpleConstraintsServiceReference', Any), ('extendableResourceReference', Any), ('specialString', Any)])):
    def __dafnystr__(self) -> str:
        return f'SimpleDependenciesTypes.SimpleDependenciesConfig.SimpleDependenciesConfig({_dafny.string_of(self.simpleResourcesConfig)}, {_dafny.string_of(self.simpleConstraintsServiceReference)}, {_dafny.string_of(self.extendableResourceReference)}, {_dafny.string_of(self.specialString)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, simple_dependencies_internaldafny_types.SimpleDependenciesConfig_SimpleDependenciesConfig) and self.simpleResourcesConfig == __o.simpleResourcesConfig and self.simpleConstraintsServiceReference == __o.simpleConstraintsServiceReference and self.extendableResourceReference == __o.extendableResourceReference and self.specialString == __o.specialString
    def __hash__(self) -> int:
        return super().__hash__()


class UseSimpleResourceInput:
    @classmethod
    def default(cls, ):
        return lambda: UseSimpleResourceInput_UseSimpleResourceInput(None, simple_resources_internaldafny_types.GetResourceDataInput.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_UseSimpleResourceInput(self) -> bool:
        return isinstance(self, simple_dependencies_internaldafny_types.UseSimpleResourceInput_UseSimpleResourceInput)

class UseSimpleResourceInput_UseSimpleResourceInput(UseSimpleResourceInput, NamedTuple('UseSimpleResourceInput', [('value', Any), ('input', Any)])):
    def __dafnystr__(self) -> str:
        return f'SimpleDependenciesTypes.UseSimpleResourceInput.UseSimpleResourceInput({_dafny.string_of(self.value)}, {_dafny.string_of(self.input)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, simple_dependencies_internaldafny_types.UseSimpleResourceInput_UseSimpleResourceInput) and self.value == __o.value and self.input == __o.input
    def __hash__(self) -> int:
        return super().__hash__()


class Error:
    @classmethod
    def default(cls, ):
        return lambda: Error_SimpleConstraints(simple_constraints_internaldafny_types.Error.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_SimpleConstraints(self) -> bool:
        return isinstance(self, simple_dependencies_internaldafny_types.Error_SimpleConstraints)
    @property
    def is_SimpleExtendableResources(self) -> bool:
        return isinstance(self, simple_dependencies_internaldafny_types.Error_SimpleExtendableResources)
    @property
    def is_SimpleResources(self) -> bool:
        return isinstance(self, simple_dependencies_internaldafny_types.Error_SimpleResources)
    @property
    def is_CollectionOfErrors(self) -> bool:
        return isinstance(self, simple_dependencies_internaldafny_types.Error_CollectionOfErrors)
    @property
    def is_Opaque(self) -> bool:
        return isinstance(self, simple_dependencies_internaldafny_types.Error_Opaque)

class Error_SimpleConstraints(Error, NamedTuple('SimpleConstraints', [('SimpleConstraints', Any)])):
    def __dafnystr__(self) -> str:
        return f'SimpleDependenciesTypes.Error.SimpleConstraints({_dafny.string_of(self.SimpleConstraints)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, simple_dependencies_internaldafny_types.Error_SimpleConstraints) and self.SimpleConstraints == __o.SimpleConstraints
    def __hash__(self) -> int:
        return super().__hash__()

class Error_SimpleExtendableResources(Error, NamedTuple('SimpleExtendableResources', [('SimpleExtendableResources', Any)])):
    def __dafnystr__(self) -> str:
        return f'SimpleDependenciesTypes.Error.SimpleExtendableResources({_dafny.string_of(self.SimpleExtendableResources)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, simple_dependencies_internaldafny_types.Error_SimpleExtendableResources) and self.SimpleExtendableResources == __o.SimpleExtendableResources
    def __hash__(self) -> int:
        return super().__hash__()

class Error_SimpleResources(Error, NamedTuple('SimpleResources', [('SimpleResources', Any)])):
    def __dafnystr__(self) -> str:
        return f'SimpleDependenciesTypes.Error.SimpleResources({_dafny.string_of(self.SimpleResources)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, simple_dependencies_internaldafny_types.Error_SimpleResources) and self.SimpleResources == __o.SimpleResources
    def __hash__(self) -> int:
        return super().__hash__()

class Error_CollectionOfErrors(Error, NamedTuple('CollectionOfErrors', [('list', Any), ('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'SimpleDependenciesTypes.Error.CollectionOfErrors({_dafny.string_of(self.list)}, {_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, simple_dependencies_internaldafny_types.Error_CollectionOfErrors) and self.list == __o.list and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_Opaque(Error, NamedTuple('Opaque', [('obj', Any)])):
    def __dafnystr__(self) -> str:
        return f'SimpleDependenciesTypes.Error.Opaque({_dafny.string_of(self.obj)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, simple_dependencies_internaldafny_types.Error_Opaque) and self.obj == __o.obj
    def __hash__(self) -> int:
        return super().__hash__()


class OpaqueError:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return simple_dependencies_internaldafny_types.Error.default()()
