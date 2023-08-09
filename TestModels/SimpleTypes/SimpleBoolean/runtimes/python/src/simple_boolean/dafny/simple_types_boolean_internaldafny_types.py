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

assert "simple_types_boolean_internaldafny_types" == __name__
simple_types_boolean_internaldafny_types = sys.modules[__name__]


class DafnyCallEvent:
    @classmethod
    def default(cls, default_I, default_O):
        return lambda: DafnyCallEvent_DafnyCallEvent(default_I(), default_O())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_DafnyCallEvent(self) -> bool:
        return isinstance(self, simple_types_boolean_internaldafny_types.DafnyCallEvent_DafnyCallEvent)

class DafnyCallEvent_DafnyCallEvent(DafnyCallEvent, NamedTuple('DafnyCallEvent', [('input', Any), ('output', Any)])):
    def __dafnystr__(self) -> str:
        return f'SimpleTypesBooleanTypes.DafnyCallEvent.DafnyCallEvent({_dafny.string_of(self.input)}, {_dafny.string_of(self.output)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, simple_types_boolean_internaldafny_types.DafnyCallEvent_DafnyCallEvent) and self.input == __o.input and self.output == __o.output
    def __hash__(self) -> int:
        return super().__hash__()


class GetBooleanInput:
    @classmethod
    def default(cls, ):
        return lambda: GetBooleanInput_GetBooleanInput(Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetBooleanInput(self) -> bool:
        return isinstance(self, simple_types_boolean_internaldafny_types.GetBooleanInput_GetBooleanInput)

class GetBooleanInput_GetBooleanInput(GetBooleanInput, NamedTuple('GetBooleanInput', [('value', Any)])):
    def __dafnystr__(self) -> str:
        return f'SimpleTypesBooleanTypes.GetBooleanInput.GetBooleanInput({_dafny.string_of(self.value)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, simple_types_boolean_internaldafny_types.GetBooleanInput_GetBooleanInput) and self.value == __o.value
    def __hash__(self) -> int:
        return super().__hash__()


class GetBooleanOutput:
    @classmethod
    def default(cls, ):
        return lambda: GetBooleanOutput_GetBooleanOutput(Wrappers.Option.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetBooleanOutput(self) -> bool:
        return isinstance(self, simple_types_boolean_internaldafny_types.GetBooleanOutput_GetBooleanOutput)

class GetBooleanOutput_GetBooleanOutput(GetBooleanOutput, NamedTuple('GetBooleanOutput', [('value', Any)])):
    def __dafnystr__(self) -> str:
        return f'SimpleTypesBooleanTypes.GetBooleanOutput.GetBooleanOutput({_dafny.string_of(self.value)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, simple_types_boolean_internaldafny_types.GetBooleanOutput_GetBooleanOutput) and self.value == __o.value
    def __hash__(self) -> int:
        return super().__hash__()


class SimpleBooleanConfig:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [SimpleBooleanConfig_SimpleBooleanConfig()]
    @classmethod
    def default(cls, ):
        return lambda: SimpleBooleanConfig_SimpleBooleanConfig()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_SimpleBooleanConfig(self) -> bool:
        return isinstance(self, simple_types_boolean_internaldafny_types.SimpleBooleanConfig_SimpleBooleanConfig)

class SimpleBooleanConfig_SimpleBooleanConfig(SimpleBooleanConfig, NamedTuple('SimpleBooleanConfig', [])):
    def __dafnystr__(self) -> str:
        return f'SimpleTypesBooleanTypes.SimpleBooleanConfig.SimpleBooleanConfig'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, simple_types_boolean_internaldafny_types.SimpleBooleanConfig_SimpleBooleanConfig)
    def __hash__(self) -> int:
        return super().__hash__()


class ISimpleTypesBooleanClientCallHistory:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "SimpleTypesBooleanTypes.ISimpleTypesBooleanClientCallHistory"

class ISimpleTypesBooleanClient:
    pass
    def GetBoolean(self, input):
        pass


class Error:
    @classmethod
    def default(cls, ):
        return lambda: Error_CollectionOfErrors(_dafny.Seq({}), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_CollectionOfErrors(self) -> bool:
        return isinstance(self, simple_types_boolean_internaldafny_types.Error_CollectionOfErrors)
    @property
    def is_Opaque(self) -> bool:
        return isinstance(self, simple_types_boolean_internaldafny_types.Error_Opaque)

class Error_CollectionOfErrors(Error, NamedTuple('CollectionOfErrors', [('list', Any), ('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'SimpleTypesBooleanTypes.Error.CollectionOfErrors({_dafny.string_of(self.list)}, {self.message.VerbatimString(True)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, simple_types_boolean_internaldafny_types.Error_CollectionOfErrors) and self.list == __o.list and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_Opaque(Error, NamedTuple('Opaque', [('obj', Any)])):
    def __dafnystr__(self) -> str:
        return f'SimpleTypesBooleanTypes.Error.Opaque({_dafny.string_of(self.obj)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, simple_types_boolean_internaldafny_types.Error_Opaque) and self.obj == __o.obj
    def __hash__(self) -> int:
        return super().__hash__()


class OpaqueError:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return simple_types_boolean_internaldafny_types.Error.default()()
