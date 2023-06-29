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

assert "simple.refinement.internaldafny.types" == __name__

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
        return f'simple.refinement.internaldafny.types_Compile.DafnyCallEvent.DafnyCallEvent({_dafny.string_of(self.input)}, {_dafny.string_of(self.output)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, DafnyCallEvent_DafnyCallEvent) and self.input == __o.input and self.output == __o.output
    def __hash__(self) -> int:
        return super().__hash__()


class GetRefinementInput:
    @classmethod
    def default(cls, ):
        return lambda: GetRefinementInput_GetRefinementInput(_dafny.Seq({}), Wrappers_Compile.Option_None.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetRefinementInput(self) -> bool:
        return isinstance(self, GetRefinementInput_GetRefinementInput)

class GetRefinementInput_GetRefinementInput(GetRefinementInput, NamedTuple('GetRefinementInput', [('requiredString', Any), ('optionalString', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.refinement.internaldafny.types_Compile.GetRefinementInput.GetRefinementInput({_dafny.string_of(self.requiredString)}, {_dafny.string_of(self.optionalString)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, GetRefinementInput_GetRefinementInput) and self.requiredString == __o.requiredString and self.optionalString == __o.optionalString
    def __hash__(self) -> int:
        return super().__hash__()


class GetRefinementOutput:
    @classmethod
    def default(cls, ):
        return lambda: GetRefinementOutput_GetRefinementOutput(_dafny.Seq({}), Wrappers_Compile.Option_None.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetRefinementOutput(self) -> bool:
        return isinstance(self, GetRefinementOutput_GetRefinementOutput)

class GetRefinementOutput_GetRefinementOutput(GetRefinementOutput, NamedTuple('GetRefinementOutput', [('requiredString', Any), ('optionalString', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.refinement.internaldafny.types_Compile.GetRefinementOutput.GetRefinementOutput({_dafny.string_of(self.requiredString)}, {_dafny.string_of(self.optionalString)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, GetRefinementOutput_GetRefinementOutput) and self.requiredString == __o.requiredString and self.optionalString == __o.optionalString
    def __hash__(self) -> int:
        return super().__hash__()


class OnlyInputInput:
    @classmethod
    def default(cls, ):
        return lambda: OnlyInputInput_OnlyInputInput(Wrappers_Compile.Option_None.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_OnlyInputInput(self) -> bool:
        return isinstance(self, OnlyInputInput_OnlyInputInput)

class OnlyInputInput_OnlyInputInput(OnlyInputInput, NamedTuple('OnlyInputInput', [('value', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.refinement.internaldafny.types_Compile.OnlyInputInput.OnlyInputInput({_dafny.string_of(self.value)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, OnlyInputInput_OnlyInputInput) and self.value == __o.value
    def __hash__(self) -> int:
        return super().__hash__()


class OnlyOutputOutput:
    @classmethod
    def default(cls, ):
        return lambda: OnlyOutputOutput_OnlyOutputOutput(Wrappers_Compile.Option_None.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_OnlyOutputOutput(self) -> bool:
        return isinstance(self, OnlyOutputOutput_OnlyOutputOutput)

class OnlyOutputOutput_OnlyOutputOutput(OnlyOutputOutput, NamedTuple('OnlyOutputOutput', [('value', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.refinement.internaldafny.types_Compile.OnlyOutputOutput.OnlyOutputOutput({_dafny.string_of(self.value)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, OnlyOutputOutput_OnlyOutputOutput) and self.value == __o.value
    def __hash__(self) -> int:
        return super().__hash__()


class ReadonlyOperationInput:
    @classmethod
    def default(cls, ):
        return lambda: ReadonlyOperationInput_ReadonlyOperationInput(_dafny.Seq({}), Wrappers_Compile.Option_None.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ReadonlyOperationInput(self) -> bool:
        return isinstance(self, ReadonlyOperationInput_ReadonlyOperationInput)

class ReadonlyOperationInput_ReadonlyOperationInput(ReadonlyOperationInput, NamedTuple('ReadonlyOperationInput', [('requiredString', Any), ('optionalString', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.refinement.internaldafny.types_Compile.ReadonlyOperationInput.ReadonlyOperationInput({_dafny.string_of(self.requiredString)}, {_dafny.string_of(self.optionalString)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, ReadonlyOperationInput_ReadonlyOperationInput) and self.requiredString == __o.requiredString and self.optionalString == __o.optionalString
    def __hash__(self) -> int:
        return super().__hash__()


class ReadonlyOperationOutput:
    @classmethod
    def default(cls, ):
        return lambda: ReadonlyOperationOutput_ReadonlyOperationOutput(_dafny.Seq({}), Wrappers_Compile.Option_None.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_ReadonlyOperationOutput(self) -> bool:
        return isinstance(self, ReadonlyOperationOutput_ReadonlyOperationOutput)

class ReadonlyOperationOutput_ReadonlyOperationOutput(ReadonlyOperationOutput, NamedTuple('ReadonlyOperationOutput', [('requiredString', Any), ('optionalString', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.refinement.internaldafny.types_Compile.ReadonlyOperationOutput.ReadonlyOperationOutput({_dafny.string_of(self.requiredString)}, {_dafny.string_of(self.optionalString)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, ReadonlyOperationOutput_ReadonlyOperationOutput) and self.requiredString == __o.requiredString and self.optionalString == __o.optionalString
    def __hash__(self) -> int:
        return super().__hash__()


class ISimpleRefinementClientCallHistory:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "simple.refinement.internaldafny.types_Compile.ISimpleRefinementClientCallHistory"

class ISimpleRefinementClient:
    pass
    def GetRefinement(self, input):
        pass

    def OnlyInput(self, input):
        pass

    def OnlyOutput(self):
        pass


class SimpleRefinementConfig:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [SimpleRefinementConfig_SimpleRefinementConfig()]
    @classmethod
    def default(cls, ):
        return lambda: SimpleRefinementConfig_SimpleRefinementConfig()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_SimpleRefinementConfig(self) -> bool:
        return isinstance(self, SimpleRefinementConfig_SimpleRefinementConfig)

class SimpleRefinementConfig_SimpleRefinementConfig(SimpleRefinementConfig, NamedTuple('SimpleRefinementConfig', [])):
    def __dafnystr__(self) -> str:
        return f'simple.refinement.internaldafny.types_Compile.SimpleRefinementConfig.SimpleRefinementConfig'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, SimpleRefinementConfig_SimpleRefinementConfig)
    def __hash__(self) -> int:
        return super().__hash__()


class Error:
    @classmethod
    def default(cls, ):
        return lambda: Error_CollectionOfErrors(_dafny.Seq({}), _dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_CollectionOfErrors(self) -> bool:
        return isinstance(self, Error_CollectionOfErrors)
    @property
    def is_Opaque(self) -> bool:
        return isinstance(self, Error_Opaque)

class Error_CollectionOfErrors(Error, NamedTuple('CollectionOfErrors', [('list', Any), ('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.refinement.internaldafny.types_Compile.Error.CollectionOfErrors({_dafny.string_of(self.list)}, {_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Error_CollectionOfErrors) and self.list == __o.list and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_Opaque(Error, NamedTuple('Opaque', [('obj', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.refinement.internaldafny.types_Compile.Error.Opaque({_dafny.string_of(self.obj)})'
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
        return Error_CollectionOfErrors.default()()

