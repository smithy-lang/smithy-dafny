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

assert "simple.types.integer.internaldafny.types" == __name__

class DafnyCallEvent:
    @classmethod
    def default(cls, default_I, default_O):
        return lambda: DafnyCallEvent_DafnyCallEvent(default_I(), default_O())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_DafnyCallEvent(self) -> bool:
        return isinstance(self, simple.types.integer.internaldafny.types.DafnyCallEvent_DafnyCallEvent)

class DafnyCallEvent_DafnyCallEvent(DafnyCallEvent, NamedTuple('DafnyCallEvent', [('input', Any), ('output', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.types.integer.internaldafny.types_Compile.DafnyCallEvent.DafnyCallEvent({_dafny.string_of(self.input)}, {_dafny.string_of(self.output)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, simple.types.integer.internaldafny.types.DafnyCallEvent_DafnyCallEvent) and self.input == __o.input and self.output == __o.output
    def __hash__(self) -> int:
        return super().__hash__()


class GetIntegerInput:
    @classmethod
    def default(cls, ):
        return lambda: GetIntegerInput_GetIntegerInput(Wrappers_Compile.Option_None.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetIntegerInput(self) -> bool:
        return isinstance(self, simple.types.integer.internaldafny.types.GetIntegerInput_GetIntegerInput)

class GetIntegerInput_GetIntegerInput(GetIntegerInput, NamedTuple('GetIntegerInput', [('value', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.types.integer.internaldafny.types_Compile.GetIntegerInput.GetIntegerInput({_dafny.string_of(self.value)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, simple.types.integer.internaldafny.types.GetIntegerInput_GetIntegerInput) and self.value == __o.value
    def __hash__(self) -> int:
        return super().__hash__()


class GetIntegerOutput:
    @classmethod
    def default(cls, ):
        return lambda: GetIntegerOutput_GetIntegerOutput(Wrappers_Compile.Option_None.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetIntegerOutput(self) -> bool:
        return isinstance(self, simple.types.integer.internaldafny.types.GetIntegerOutput_GetIntegerOutput)

class GetIntegerOutput_GetIntegerOutput(GetIntegerOutput, NamedTuple('GetIntegerOutput', [('value', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.types.integer.internaldafny.types_Compile.GetIntegerOutput.GetIntegerOutput({_dafny.string_of(self.value)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, simple.types.integer.internaldafny.types.GetIntegerOutput_GetIntegerOutput) and self.value == __o.value
    def __hash__(self) -> int:
        return super().__hash__()


class SimpleIntegerConfig:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [SimpleIntegerConfig_SimpleIntegerConfig()]
    @classmethod
    def default(cls, ):
        return lambda: SimpleIntegerConfig_SimpleIntegerConfig()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_SimpleIntegerConfig(self) -> bool:
        return isinstance(self, simple.types.integer.internaldafny.types.SimpleIntegerConfig_SimpleIntegerConfig)

class SimpleIntegerConfig_SimpleIntegerConfig(SimpleIntegerConfig, NamedTuple('SimpleIntegerConfig', [])):
    def __dafnystr__(self) -> str:
        return f'simple.types.integer.internaldafny.types_Compile.SimpleIntegerConfig.SimpleIntegerConfig'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, simple.types.integer.internaldafny.types.SimpleIntegerConfig_SimpleIntegerConfig)
    def __hash__(self) -> int:
        return super().__hash__()


class ISimpleTypesIntegerClientCallHistory:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "simple.types.integer.internaldafny.types_Compile.ISimpleTypesIntegerClientCallHistory"

class ISimpleTypesIntegerClient:
    pass
    def GetInteger(self, input):
        pass

    def GetIntegerKnownValueTest(self, input):
        pass


class Error:
    @classmethod
    def default(cls, ):
        return lambda: Error_CollectionOfErrors(_dafny.Seq({}), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_CollectionOfErrors(self) -> bool:
        return isinstance(self, simple.types.integer.internaldafny.types.Error_CollectionOfErrors)
    @property
    def is_Opaque(self) -> bool:
        return isinstance(self, simple.types.integer.internaldafny.types.Error_Opaque)

class Error_CollectionOfErrors(Error, NamedTuple('CollectionOfErrors', [('list', Any), ('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.types.integer.internaldafny.types_Compile.Error.CollectionOfErrors({_dafny.string_of(self.list)}, {_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, simple.types.integer.internaldafny.types.Error_CollectionOfErrors) and self.list == __o.list and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_Opaque(Error, NamedTuple('Opaque', [('obj', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.types.integer.internaldafny.types_Compile.Error.Opaque({_dafny.string_of(self.obj)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, simple.types.integer.internaldafny.types.Error_Opaque) and self.obj == __o.obj
    def __hash__(self) -> int:
        return super().__hash__()


class OpaqueError:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return ""
    @staticmethod
    def default():
        return simple.types.integer.internaldafny.types.Error_CollectionOfErrors.default()()

