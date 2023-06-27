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

assert "simple.errors.internaldafny.types" == __name__

class DafnyCallEvent:
    @classmethod
    def default(cls, default_I, default_O):
        return lambda: DafnyCallEvent_DafnyCallEvent(default_I(), default_O())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_DafnyCallEvent(self) -> bool:
        return isinstance(self, DafnyCallEvent_DafnyCallEvent)

class DafnyCallEvent_DafnyCallEvent(DafnyCallEvent, NamedTuple('DafnyCallEvent', [('input', Any), ('output', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.errors.internaldafny.types_Compile.DafnyCallEvent.DafnyCallEvent({_dafny.string_of(self.input)}, {_dafny.string_of(self.output)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, DafnyCallEvent_DafnyCallEvent) and self.input == __o.input and self.output == __o.output
    def __hash__(self) -> int:
        return super().__hash__()


class GetErrorsInput:
    @classmethod
    def default(cls, ):
        return lambda: GetErrorsInput_GetErrorsInput(Wrappers_Compile.Option_None.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetErrorsInput(self) -> bool:
        return isinstance(self, GetErrorsInput_GetErrorsInput)

class GetErrorsInput_GetErrorsInput(GetErrorsInput, NamedTuple('GetErrorsInput', [('value', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.errors.internaldafny.types_Compile.GetErrorsInput.GetErrorsInput({_dafny.string_of(self.value)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, GetErrorsInput_GetErrorsInput) and self.value == __o.value
    def __hash__(self) -> int:
        return super().__hash__()


class GetErrorsOutput:
    @classmethod
    def default(cls, ):
        return lambda: GetErrorsOutput_GetErrorsOutput(Wrappers_Compile.Option_None.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetErrorsOutput(self) -> bool:
        return isinstance(self, GetErrorsOutput_GetErrorsOutput)

class GetErrorsOutput_GetErrorsOutput(GetErrorsOutput, NamedTuple('GetErrorsOutput', [('value', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.errors.internaldafny.types_Compile.GetErrorsOutput.GetErrorsOutput({_dafny.string_of(self.value)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, GetErrorsOutput_GetErrorsOutput) and self.value == __o.value
    def __hash__(self) -> int:
        return super().__hash__()


class ISimpleErrorsClientCallHistory:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "simple.errors.internaldafny.types_Compile.ISimpleErrorsClientCallHistory"

class ISimpleErrorsClient:
    pass
    def AlwaysError(self, input):
        pass

    def AlwaysMultipleErrors(self, input):
        pass

    def AlwaysNativeError(self, input):
        pass


class SimpleErrorsConfig:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [SimpleErrorsConfig_SimpleErrorsConfig()]
    @classmethod
    def default(cls, ):
        return lambda: SimpleErrorsConfig_SimpleErrorsConfig()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_SimpleErrorsConfig(self) -> bool:
        return isinstance(self, SimpleErrorsConfig_SimpleErrorsConfig)

class SimpleErrorsConfig_SimpleErrorsConfig(SimpleErrorsConfig, NamedTuple('SimpleErrorsConfig', [])):
    def __dafnystr__(self) -> str:
        return f'simple.errors.internaldafny.types_Compile.SimpleErrorsConfig.SimpleErrorsConfig'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, SimpleErrorsConfig_SimpleErrorsConfig)
    def __hash__(self) -> int:
        return super().__hash__()


class Error:
    @classmethod
    def default(cls, ):
        return lambda: Error_SimpleErrorsException(_dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_SimpleErrorsException(self) -> bool:
        return isinstance(self, Error_SimpleErrorsException)
    @property
    def is_CollectionOfErrors(self) -> bool:
        return isinstance(self, Error_CollectionOfErrors)
    @property
    def is_Opaque(self) -> bool:
        return isinstance(self, Error_Opaque)

class Error_SimpleErrorsException(Error, NamedTuple('SimpleErrorsException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.errors.internaldafny.types_Compile.Error.SimpleErrorsException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Error_SimpleErrorsException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_CollectionOfErrors(Error, NamedTuple('CollectionOfErrors', [('list', Any), ('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.errors.internaldafny.types_Compile.Error.CollectionOfErrors({_dafny.string_of(self.list)}, {_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Error_CollectionOfErrors) and self.list == __o.list and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_Opaque(Error, NamedTuple('Opaque', [('obj', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.errors.internaldafny.types_Compile.Error.Opaque({_dafny.string_of(self.obj)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Error_Opaque) and self.obj == __o.obj
    def __hash__(self) -> int:
        return super().__hash__()


class OpaqueError:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return ""
    @staticmethod
    def default():
        return Error_SimpleErrorsException.default()()

