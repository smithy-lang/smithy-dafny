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

assert "simple.extendable.resources.internaldafny.types" == __name__

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
        return f'simple.extendable.resources.internaldafny.types_Compile.DafnyCallEvent.DafnyCallEvent({_dafny.string_of(self.input)}, {_dafny.string_of(self.output)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, DafnyCallEvent_DafnyCallEvent) and self.input == __o.input and self.output == __o.output
    def __hash__(self) -> int:
        return super().__hash__()


class CreateExtendableResourceInput:
    @classmethod
    def default(cls, ):
        return lambda: CreateExtendableResourceInput_CreateExtendableResourceInput(_dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_CreateExtendableResourceInput(self) -> bool:
        return isinstance(self, CreateExtendableResourceInput_CreateExtendableResourceInput)

class CreateExtendableResourceInput_CreateExtendableResourceInput(CreateExtendableResourceInput, NamedTuple('CreateExtendableResourceInput', [('name', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.extendable.resources.internaldafny.types_Compile.CreateExtendableResourceInput.CreateExtendableResourceInput({_dafny.string_of(self.name)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, CreateExtendableResourceInput_CreateExtendableResourceInput) and self.name == __o.name
    def __hash__(self) -> int:
        return super().__hash__()


class CreateExtendableResourceOutput:
    @classmethod
    def default(cls, ):
        return lambda: CreateExtendableResourceOutput_CreateExtendableResourceOutput(None)
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_CreateExtendableResourceOutput(self) -> bool:
        return isinstance(self, CreateExtendableResourceOutput_CreateExtendableResourceOutput)

class CreateExtendableResourceOutput_CreateExtendableResourceOutput(CreateExtendableResourceOutput, NamedTuple('CreateExtendableResourceOutput', [('resource', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.extendable.resources.internaldafny.types_Compile.CreateExtendableResourceOutput.CreateExtendableResourceOutput({_dafny.string_of(self.resource)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, CreateExtendableResourceOutput_CreateExtendableResourceOutput) and self.resource == __o.resource
    def __hash__(self) -> int:
        return super().__hash__()


class IExtendableResourceCallHistory:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "simple.extendable.resources.internaldafny.types_Compile.IExtendableResourceCallHistory"

class IExtendableResource:
    pass
    @staticmethod
    def GetExtendableResourceData(self, input):
        pass

    @staticmethod
    def GetExtendableResourceData(self, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(GetExtendableResourceDataOutput.default())()
        out0_: Wrappers_Compile.Result
        out0_ = (self).GetExtendableResourceData_k(input)
        output = out0_
        return output

    def GetExtendableResourceData_k(self, input):
        pass

    @staticmethod
    def AlwaysMultipleErrors(self, input):
        pass

    @staticmethod
    def AlwaysMultipleErrors(self, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(GetExtendableResourceErrorsOutput.default())()
        out1_: Wrappers_Compile.Result
        out1_ = (self).AlwaysMultipleErrors_k(input)
        output = out1_
        return output

    def AlwaysMultipleErrors_k(self, input):
        pass

    @staticmethod
    def AlwaysModeledError(self, input):
        pass

    @staticmethod
    def AlwaysModeledError(self, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(GetExtendableResourceErrorsOutput.default())()
        out2_: Wrappers_Compile.Result
        out2_ = (self).AlwaysModeledError_k(input)
        output = out2_
        return output

    def AlwaysModeledError_k(self, input):
        pass

    @staticmethod
    def AlwaysOpaqueError(self, input):
        pass

    @staticmethod
    def AlwaysOpaqueError(self, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(GetExtendableResourceErrorsOutput.default())()
        out3_: Wrappers_Compile.Result
        out3_ = (self).AlwaysOpaqueError_k(input)
        output = out3_
        return output

    def AlwaysOpaqueError_k(self, input):
        pass


class GetExtendableResourceDataInput:
    @classmethod
    def default(cls, ):
        return lambda: GetExtendableResourceDataInput_GetExtendableResourceDataInput(Wrappers_Compile.Option_None.default()(), Wrappers_Compile.Option_None.default()(), Wrappers_Compile.Option_None.default()(), Wrappers_Compile.Option_None.default()(), Wrappers_Compile.Option_None.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetExtendableResourceDataInput(self) -> bool:
        return isinstance(self, GetExtendableResourceDataInput_GetExtendableResourceDataInput)

class GetExtendableResourceDataInput_GetExtendableResourceDataInput(GetExtendableResourceDataInput, NamedTuple('GetExtendableResourceDataInput', [('blobValue', Any), ('booleanValue', Any), ('stringValue', Any), ('integerValue', Any), ('longValue', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.extendable.resources.internaldafny.types_Compile.GetExtendableResourceDataInput.GetExtendableResourceDataInput({_dafny.string_of(self.blobValue)}, {_dafny.string_of(self.booleanValue)}, {_dafny.string_of(self.stringValue)}, {_dafny.string_of(self.integerValue)}, {_dafny.string_of(self.longValue)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, GetExtendableResourceDataInput_GetExtendableResourceDataInput) and self.blobValue == __o.blobValue and self.booleanValue == __o.booleanValue and self.stringValue == __o.stringValue and self.integerValue == __o.integerValue and self.longValue == __o.longValue
    def __hash__(self) -> int:
        return super().__hash__()


class GetExtendableResourceDataOutput:
    @classmethod
    def default(cls, ):
        return lambda: GetExtendableResourceDataOutput_GetExtendableResourceDataOutput(Wrappers_Compile.Option_None.default()(), Wrappers_Compile.Option_None.default()(), Wrappers_Compile.Option_None.default()(), Wrappers_Compile.Option_None.default()(), Wrappers_Compile.Option_None.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetExtendableResourceDataOutput(self) -> bool:
        return isinstance(self, GetExtendableResourceDataOutput_GetExtendableResourceDataOutput)

class GetExtendableResourceDataOutput_GetExtendableResourceDataOutput(GetExtendableResourceDataOutput, NamedTuple('GetExtendableResourceDataOutput', [('blobValue', Any), ('booleanValue', Any), ('stringValue', Any), ('integerValue', Any), ('longValue', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.extendable.resources.internaldafny.types_Compile.GetExtendableResourceDataOutput.GetExtendableResourceDataOutput({_dafny.string_of(self.blobValue)}, {_dafny.string_of(self.booleanValue)}, {_dafny.string_of(self.stringValue)}, {_dafny.string_of(self.integerValue)}, {_dafny.string_of(self.longValue)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, GetExtendableResourceDataOutput_GetExtendableResourceDataOutput) and self.blobValue == __o.blobValue and self.booleanValue == __o.booleanValue and self.stringValue == __o.stringValue and self.integerValue == __o.integerValue and self.longValue == __o.longValue
    def __hash__(self) -> int:
        return super().__hash__()


class GetExtendableResourceErrorsInput:
    @classmethod
    def default(cls, ):
        return lambda: GetExtendableResourceErrorsInput_GetExtendableResourceErrorsInput(Wrappers_Compile.Option_None.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetExtendableResourceErrorsInput(self) -> bool:
        return isinstance(self, GetExtendableResourceErrorsInput_GetExtendableResourceErrorsInput)

class GetExtendableResourceErrorsInput_GetExtendableResourceErrorsInput(GetExtendableResourceErrorsInput, NamedTuple('GetExtendableResourceErrorsInput', [('value', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.extendable.resources.internaldafny.types_Compile.GetExtendableResourceErrorsInput.GetExtendableResourceErrorsInput({_dafny.string_of(self.value)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, GetExtendableResourceErrorsInput_GetExtendableResourceErrorsInput) and self.value == __o.value
    def __hash__(self) -> int:
        return super().__hash__()


class GetExtendableResourceErrorsOutput:
    @classmethod
    def default(cls, ):
        return lambda: GetExtendableResourceErrorsOutput_GetExtendableResourceErrorsOutput(Wrappers_Compile.Option_None.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_GetExtendableResourceErrorsOutput(self) -> bool:
        return isinstance(self, GetExtendableResourceErrorsOutput_GetExtendableResourceErrorsOutput)

class GetExtendableResourceErrorsOutput_GetExtendableResourceErrorsOutput(GetExtendableResourceErrorsOutput, NamedTuple('GetExtendableResourceErrorsOutput', [('value', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.extendable.resources.internaldafny.types_Compile.GetExtendableResourceErrorsOutput.GetExtendableResourceErrorsOutput({_dafny.string_of(self.value)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, GetExtendableResourceErrorsOutput_GetExtendableResourceErrorsOutput) and self.value == __o.value
    def __hash__(self) -> int:
        return super().__hash__()


class Name:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return ""
    @staticmethod
    def default():
        return _dafny.Seq({})

class ISimpleExtendableResourcesClientCallHistory:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "simple.extendable.resources.internaldafny.types_Compile.ISimpleExtendableResourcesClientCallHistory"

class ISimpleExtendableResourcesClient:
    pass
    def CreateExtendableResource(self, input):
        pass

    def UseExtendableResource(self, input):
        pass

    def UseExtendableResourceAlwaysModeledError(self, input):
        pass

    def UseExtendableResourceAlwaysMultipleErrors(self, input):
        pass

    def UseExtendableResourceAlwaysOpaqueError(self, input):
        pass


class SimpleExtendableResourcesConfig:
    @_dafny.classproperty
    def AllSingletonConstructors(cls):
        return [SimpleExtendableResourcesConfig_SimpleExtendableResourcesConfig()]
    @classmethod
    def default(cls, ):
        return lambda: SimpleExtendableResourcesConfig_SimpleExtendableResourcesConfig()
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_SimpleExtendableResourcesConfig(self) -> bool:
        return isinstance(self, SimpleExtendableResourcesConfig_SimpleExtendableResourcesConfig)

class SimpleExtendableResourcesConfig_SimpleExtendableResourcesConfig(SimpleExtendableResourcesConfig, NamedTuple('SimpleExtendableResourcesConfig', [])):
    def __dafnystr__(self) -> str:
        return f'simple.extendable.resources.internaldafny.types_Compile.SimpleExtendableResourcesConfig.SimpleExtendableResourcesConfig'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, SimpleExtendableResourcesConfig_SimpleExtendableResourcesConfig)
    def __hash__(self) -> int:
        return super().__hash__()


class UseExtendableResourceErrorsInput:
    @classmethod
    def default(cls, ):
        return lambda: UseExtendableResourceErrorsInput_UseExtendableResourceErrorsInput(None, GetExtendableResourceErrorsInput_GetExtendableResourceErrorsInput.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_UseExtendableResourceErrorsInput(self) -> bool:
        return isinstance(self, UseExtendableResourceErrorsInput_UseExtendableResourceErrorsInput)

class UseExtendableResourceErrorsInput_UseExtendableResourceErrorsInput(UseExtendableResourceErrorsInput, NamedTuple('UseExtendableResourceErrorsInput', [('resource', Any), ('input', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.extendable.resources.internaldafny.types_Compile.UseExtendableResourceErrorsInput.UseExtendableResourceErrorsInput({_dafny.string_of(self.resource)}, {_dafny.string_of(self.input)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, UseExtendableResourceErrorsInput_UseExtendableResourceErrorsInput) and self.resource == __o.resource and self.input == __o.input
    def __hash__(self) -> int:
        return super().__hash__()


class UseExtendableResourceInput:
    @classmethod
    def default(cls, ):
        return lambda: UseExtendableResourceInput_UseExtendableResourceInput(None, GetExtendableResourceDataInput_GetExtendableResourceDataInput.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_UseExtendableResourceInput(self) -> bool:
        return isinstance(self, UseExtendableResourceInput_UseExtendableResourceInput)

class UseExtendableResourceInput_UseExtendableResourceInput(UseExtendableResourceInput, NamedTuple('UseExtendableResourceInput', [('resource', Any), ('input', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.extendable.resources.internaldafny.types_Compile.UseExtendableResourceInput.UseExtendableResourceInput({_dafny.string_of(self.resource)}, {_dafny.string_of(self.input)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, UseExtendableResourceInput_UseExtendableResourceInput) and self.resource == __o.resource and self.input == __o.input
    def __hash__(self) -> int:
        return super().__hash__()


class UseExtendableResourceOutput:
    @classmethod
    def default(cls, ):
        return lambda: UseExtendableResourceOutput_UseExtendableResourceOutput(GetExtendableResourceDataOutput_GetExtendableResourceDataOutput.default()())
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_UseExtendableResourceOutput(self) -> bool:
        return isinstance(self, UseExtendableResourceOutput_UseExtendableResourceOutput)

class UseExtendableResourceOutput_UseExtendableResourceOutput(UseExtendableResourceOutput, NamedTuple('UseExtendableResourceOutput', [('output', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.extendable.resources.internaldafny.types_Compile.UseExtendableResourceOutput.UseExtendableResourceOutput({_dafny.string_of(self.output)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, UseExtendableResourceOutput_UseExtendableResourceOutput) and self.output == __o.output
    def __hash__(self) -> int:
        return super().__hash__()


class Error:
    @classmethod
    def default(cls, ):
        return lambda: Error_SimpleExtendableResourcesException(_dafny.Seq({}))
    def __ne__(self, __o: object) -> bool:
        return not self.__eq__(__o)
    @property
    def is_SimpleExtendableResourcesException(self) -> bool:
        return isinstance(self, Error_SimpleExtendableResourcesException)
    @property
    def is_CollectionOfErrors(self) -> bool:
        return isinstance(self, Error_CollectionOfErrors)
    @property
    def is_Opaque(self) -> bool:
        return isinstance(self, Error_Opaque)

class Error_SimpleExtendableResourcesException(Error, NamedTuple('SimpleExtendableResourcesException', [('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.extendable.resources.internaldafny.types_Compile.Error.SimpleExtendableResourcesException({_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Error_SimpleExtendableResourcesException) and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_CollectionOfErrors(Error, NamedTuple('CollectionOfErrors', [('list', Any), ('message', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.extendable.resources.internaldafny.types_Compile.Error.CollectionOfErrors({_dafny.string_of(self.list)}, {_dafny.string_of(self.message)})'
    def __eq__(self, __o: object) -> bool:
        return isinstance(__o, Error_CollectionOfErrors) and self.list == __o.list and self.message == __o.message
    def __hash__(self) -> int:
        return super().__hash__()

class Error_Opaque(Error, NamedTuple('Opaque', [('obj', Any)])):
    def __dafnystr__(self) -> str:
        return f'simple.extendable.resources.internaldafny.types_Compile.Error.Opaque({_dafny.string_of(self.obj)})'
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
        return Error_SimpleExtendableResourcesException.default()()

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "simple.extendable.resources.internaldafny.types_Compile._default"
    @staticmethod
    def IsValid__Name(x):
        return (1) <= (len(x))

