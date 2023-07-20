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

assert "simple.resources.internaldafny.types" == __name__

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
        return f'simple.resources.internaldafny.types_Compile.DafnyCallEvent.DafnyCallEvent({_dafny.string_of(self.input)}, {_dafny.string_of(self.output)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, DafnyCallEvent_DafnyCallEvent) and self.input == __o.input and self.output == __o.output
    def __hash__(self) -> int:
        return super().__hash__()


class GetResourceDataInput:
    @classmethod
    def default(cls, ):
        return lambda: GetResourceDataInput_GetResourceDataInput(Wrappers_Compile.Option_None.default()(), Wrappers_Compile.Option_None.default()(), Wrappers_Compile.Option_None.default()(), Wrappers_Compile.Option_None.default()(), Wrappers_Compile.Option_None.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetResourceDataInput(self) -> bool:
        return isinstance(self, GetResourceDataInput_GetResourceDataInput)

class GetResourceDataInput_GetResourceDataInput(GetResourceDataInput, NamedTuple('GetResourceDataInput', [('blobValue', Any), ('booleanValue', Any), ('stringValue', Any), ('integerValue', Any), ('longValue', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.resources.internaldafny.types_Compile.GetResourceDataInput.GetResourceDataInput({_dafny.string_of(self.blobValue)}, {_dafny.string_of(self.booleanValue)}, {_dafny.string_of(self.stringValue)}, {_dafny.string_of(self.integerValue)}, {_dafny.string_of(self.longValue)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, GetResourceDataInput_GetResourceDataInput) and self.blobValue == __o.blobValue and self.booleanValue == __o.booleanValue and self.stringValue == __o.stringValue and self.integerValue == __o.integerValue and self.longValue == __o.longValue
    def __hash__(self) -> int:
        return super().__hash__()


class GetResourceDataOutput:
    @classmethod
    def default(cls, ):
        return lambda: GetResourceDataOutput_GetResourceDataOutput(Wrappers_Compile.Option_None.default()(), Wrappers_Compile.Option_None.default()(), Wrappers_Compile.Option_None.default()(), Wrappers_Compile.Option_None.default()(), Wrappers_Compile.Option_None.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetResourceDataOutput(self) -> bool:
        return isinstance(self, GetResourceDataOutput_GetResourceDataOutput)

class GetResourceDataOutput_GetResourceDataOutput(GetResourceDataOutput, NamedTuple('GetResourceDataOutput', [('blobValue', Any), ('booleanValue', Any), ('stringValue', Any), ('integerValue', Any), ('longValue', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.resources.internaldafny.types_Compile.GetResourceDataOutput.GetResourceDataOutput({_dafny.string_of(self.blobValue)}, {_dafny.string_of(self.booleanValue)}, {_dafny.string_of(self.stringValue)}, {_dafny.string_of(self.integerValue)}, {_dafny.string_of(self.longValue)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, GetResourceDataOutput_GetResourceDataOutput) and self.blobValue == __o.blobValue and self.booleanValue == __o.booleanValue and self.stringValue == __o.stringValue and self.integerValue == __o.integerValue and self.longValue == __o.longValue
    def __hash__(self) -> int:
        return super().__hash__()


class GetResourcesInput:
    @classmethod
    def default(cls, ):
        return lambda: GetResourcesInput_GetResourcesInput(Wrappers_Compile.Option_None.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetResourcesInput(self) -> bool:
        return isinstance(self, GetResourcesInput_GetResourcesInput)

class GetResourcesInput_GetResourcesInput(GetResourcesInput, NamedTuple('GetResourcesInput', [('value', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.resources.internaldafny.types_Compile.GetResourcesInput.GetResourcesInput({_dafny.string_of(self.value)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, GetResourcesInput_GetResourcesInput) and self.value == __o.value
    def __hash__(self) -> int:
        return super().__hash__()


class GetResourcesOutput:
    @classmethod
    def default(cls, ):
        return lambda: GetResourcesOutput_GetResourcesOutput(None)
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetResourcesOutput(self) -> bool:
        return isinstance(self, GetResourcesOutput_GetResourcesOutput)

class GetResourcesOutput_GetResourcesOutput(GetResourcesOutput, NamedTuple('GetResourcesOutput', [('output', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.resources.internaldafny.types_Compile.GetResourcesOutput.GetResourcesOutput({_dafny.string_of(self.output)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, GetResourcesOutput_GetResourcesOutput) and self.output == __o.output
    def __hash__(self) -> int:
        return super().__hash__()


class ISimpleResourceCallHistory:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "simple.resources.internaldafny.types_Compile.ISimpleResourceCallHistory"

class ISimpleResource:
    def GetResourceData(self, input):
        pass

    def GetResourceData(self, input):
        print("nononononononononononononono")
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(GetResourceDataOutput.default())()
        out0_: Wrappers_Compile.Result
        out0_ = (self).GetResourceData_k(input)
        output = out0_
        return output

    def GetResourceData_k(self, input):
        pass


class ISimpleResourcesClientCallHistory:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "simple.resources.internaldafny.types_Compile.ISimpleResourcesClientCallHistory"

class ISimpleResourcesClient:
    pass
    def GetResources(self, input):
        pass


class SimpleResourcesConfig:
    @classmethod
    def default(cls, ):
        return lambda: SimpleResourcesConfig_SimpleResourcesConfig(_dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_SimpleResourcesConfig(self) -> bool:
        return isinstance(self, SimpleResourcesConfig_SimpleResourcesConfig)

class SimpleResourcesConfig_SimpleResourcesConfig(SimpleResourcesConfig, NamedTuple('SimpleResourcesConfig', [('name', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.resources.internaldafny.types_Compile.SimpleResourcesConfig.SimpleResourcesConfig({_dafny.string_of(self.name)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, SimpleResourcesConfig_SimpleResourcesConfig) and self.name == __o.name
    def __hash__(self) -> int:
        return super().__hash__()


class Error:
    @classmethod
    def default(cls, ):
        return lambda: Error_SimpleResourcesException(_dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_SimpleResourcesException(self) -> bool:
        return isinstance(self, Error_SimpleResourcesException)
    @property
    def is_CollectionOfErrors(self) -> bool:
        return isinstance(self, Error_CollectionOfErrors)
    @property
    def is_Opaque(self) -> bool:
        return isinstance(self, Error_Opaque)

class Error_SimpleResourcesException(Error, NamedTuple('SimpleResourcesException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.resources.internaldafny.types_Compile.Error.SimpleResourcesException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Error_SimpleResourcesException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_CollectionOfErrors(Error, NamedTuple('CollectionOfErrors', [('list', Any), ('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.resources.internaldafny.types_Compile.Error.CollectionOfErrors({_dafny.string_of(self.list)}, {_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Error_CollectionOfErrors) and self.list == __o.list and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_Opaque(Error, NamedTuple('Opaque', [('obj', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.resources.internaldafny.types_Compile.Error.Opaque({_dafny.string_of(self.obj)})'
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
        return Error_SimpleResourcesException.default()()

