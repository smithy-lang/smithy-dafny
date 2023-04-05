import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import Wrappers_Compile
import Dafny.Simpletypes.Boolean

class DafnyCallEvent:
    @classmethod
    def default(cls, default_I, default_O):
        return lambda: DafnyCallEvent_DafnyCallEvent(default_I(), default_O())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_DafnyCallEvent(self) -> bool:
        return isinstance(self, Dafny.Simpletypes.Boolean.Types.DafnyCallEvent_DafnyCallEvent)

class DafnyCallEvent_DafnyCallEvent(DafnyCallEvent, NamedTuple('DafnyCallEvent', [('input', Any), ('output', Any)])):
    def __dafnystr__(self) -> str:
        return f'Dafny.Simpletypes.Boolean.Types_Compile.DafnyCallEvent.DafnyCallEvent({_dafny.string_of(self.input)}, {_dafny.string_of(self.output)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Dafny.Simpletypes.Boolean.Types.DafnyCallEvent_DafnyCallEvent) and self.input == __o.input and self.output == __o.output
    def __hash__(self) -> int:
        return super().__hash__()


class GetBooleanInput:
    @classmethod
    def default(cls, ):
        return lambda: GetBooleanInput_GetBooleanInput(Wrappers_Compile.Option_None.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetBooleanInput(self) -> bool:
        return isinstance(self, Dafny.Simpletypes.Boolean.Types.GetBooleanInput_GetBooleanInput)

class GetBooleanInput_GetBooleanInput(GetBooleanInput, NamedTuple('GetBooleanInput', [('value', Any)])):
    def __dafnystr__(self) -> str:
        return f'Dafny.Simpletypes.Boolean.Types_Compile.GetBooleanInput.GetBooleanInput({_dafny.string_of(self.value)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Dafny.Simpletypes.Boolean.Types.GetBooleanInput_GetBooleanInput) and self.value == __o.value
    def __hash__(self) -> int:
        return super().__hash__()


class GetBooleanOutput:
    @classmethod
    def default(cls, ):
        return lambda: GetBooleanOutput_GetBooleanOutput(Wrappers_Compile.Option_None.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetBooleanOutput(self) -> bool:
        return isinstance(self, Dafny.Simpletypes.Boolean.Types.GetBooleanOutput_GetBooleanOutput)

class GetBooleanOutput_GetBooleanOutput(GetBooleanOutput, NamedTuple('GetBooleanOutput', [('value', Any)])):
    def __dafnystr__(self) -> str:
        return f'Dafny.Simpletypes.Boolean.Types_Compile.GetBooleanOutput.GetBooleanOutput({_dafny.string_of(self.value)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Dafny.Simpletypes.Boolean.Types.GetBooleanOutput_GetBooleanOutput) and self.value == __o.value
    def __hash__(self) -> int:
        return super().__hash__()


class ISimpleBooleanClientCallHistory:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "Dafny.Simpletypes.Boolean.Types_Compile.ISimpleBooleanClientCallHistory"

class ISimpleBooleanClient:
    pass
    def GetBoolean(self, input):
        pass


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
        return isinstance(self, Dafny.Simpletypes.Boolean.Types.SimpleBooleanConfig_SimpleBooleanConfig)

class SimpleBooleanConfig_SimpleBooleanConfig(SimpleBooleanConfig, NamedTuple('SimpleBooleanConfig', [])):
    def __dafnystr__(self) -> str:
        return f'Dafny.Simpletypes.Boolean.Types_Compile.SimpleBooleanConfig.SimpleBooleanConfig'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Dafny.Simpletypes.Boolean.Types.SimpleBooleanConfig_SimpleBooleanConfig)
    def __hash__(self) -> int:
        return super().__hash__()


class Error:
    @classmethod
    def default(cls, ):
        return lambda: Error_CollectionOfErrors(_dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_CollectionOfErrors(self) -> bool:
        return isinstance(self, Dafny.Simpletypes.Boolean.Types.Error_CollectionOfErrors)
    @property
    def is_Opaque(self) -> bool:
        return isinstance(self, Dafny.Simpletypes.Boolean.Types.Error_Opaque)

class Error_CollectionOfErrors(Error, NamedTuple('CollectionOfErrors', [('list', Any)])):
    def __dafnystr__(self) -> str:
        return f'Dafny.Simpletypes.Boolean.Types_Compile.Error.CollectionOfErrors({_dafny.string_of(self.list)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Dafny.Simpletypes.Boolean.Types.Error_CollectionOfErrors) and self.list == __o.list
    def __hash__(self) -> int:
        return super().__hash__()

class Error_Opaque(Error, NamedTuple('Opaque', [('obj', Any)])):
    def __dafnystr__(self) -> str:
        return f'Dafny.Simpletypes.Boolean.Types_Compile.Error.Opaque({_dafny.string_of(self.obj)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Dafny.Simpletypes.Boolean.Types.Error_Opaque) and self.obj == __o.obj
    def __hash__(self) -> int:
        return super().__hash__()


class OpaqueError:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return ""
    @staticmethod
    def default():
        return Dafny.Simpletypes.Boolean.Types.Error_CollectionOfErrors.default()()

