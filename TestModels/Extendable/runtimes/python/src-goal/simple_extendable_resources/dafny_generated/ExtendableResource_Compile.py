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
import simple.extendable.resources.internaldafny.types

assert "ExtendableResource_Compile" == __name__
ExtendableResource_Compile = sys.modules[__name__]

class OpaqueMessage:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "ExtendableResource_Compile.OpaqueMessage"
    def ctor__(self):
        pass
        pass

    @property
    def message(self):
        return _dafny.Seq("Hard Coded Opaque Message that will not survive translation.")

class ExtendableResource(simple.extendable.resources.internaldafny.types.IExtendableResource):
    def  __init__(self):
        self._name: _dafny.Seq = _dafny.Seq({})
        pass

    def __dafnystr__(self) -> str:
        return "ExtendableResource_Compile.ExtendableResource"
    def GetExtendableResourceData(self, input):
        out4_: Wrappers_Compile.Result
        out4_ = simple.extendable.resources.internaldafny.types.IExtendableResource.GetExtendableResourceData(self, input)
        return out4_

    def AlwaysMultipleErrors(self, input):
        out5_: Wrappers_Compile.Result
        out5_ = simple.extendable.resources.internaldafny.types.IExtendableResource.AlwaysMultipleErrors(self, input)
        return out5_

    def AlwaysModeledError(self, input):
        out6_: Wrappers_Compile.Result
        out6_ = simple.extendable.resources.internaldafny.types.IExtendableResource.AlwaysModeledError(self, input)
        return out6_

    def AlwaysOpaqueError(self, input):
        out7_: Wrappers_Compile.Result
        out7_ = simple.extendable.resources.internaldafny.types.IExtendableResource.AlwaysOpaqueError(self, input)
        return out7_

    def ctor__(self):
        (self)._name = (ExtendableResource_Compile.default__).DEFAULT__RESOURCE__NAME

    def OfName(self, name):
        (self)._name = name

    def AlwaysMultipleErrors_k(self, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsOutput.default())()
        d_71_nestedError_: simple.extendable.resources.internaldafny.types.Error
        d_71_nestedError_ = simple.extendable.resources.internaldafny.types.Error_SimpleExtendableResourcesException(_dafny.Seq("Hard Coded Modeled Exception in Collection"))
        output = Wrappers_Compile.Result_Failure(simple.extendable.resources.internaldafny.types.Error_CollectionOfErrors(_dafny.Seq([d_71_nestedError_]), _dafny.Seq("Something")))
        return output
        return output

    def GetExtendableResourceData_k(self, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.extendable.resources.internaldafny.types.GetExtendableResourceDataOutput.default())()
        d_72_rtnString_: _dafny.Seq
        d_72_rtnString_ = (((((input).stringValue).value) + (_dafny.Seq(" "))) + ((self).name) if ((input).stringValue).is_Some else (self).name)
        d_73_rtn_: simple.extendable.resources.internaldafny.types.GetExtendableResourceDataOutput
        d_73_rtn_ = simple.extendable.resources.internaldafny.types.GetExtendableResourceDataOutput_GetExtendableResourceDataOutput((input).blobValue, (input).booleanValue, Wrappers_Compile.Option_Some(d_72_rtnString_), (input).integerValue, (input).longValue)
        output = Wrappers_Compile.Result_Success(d_73_rtn_)
        return output
        return output

    def AlwaysModeledError_k(self, input):
        print("AlwaysModeledError_k")
        print(input)
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsOutput.default())()
        output = Wrappers_Compile.Result_Failure(simple.extendable.resources.internaldafny.types.Error_SimpleExtendableResourcesException(_dafny.Seq("Hard Coded Exception in src/dafny")))
        return output
        return output

    def AlwaysOpaqueError_k(self, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.extendable.resources.internaldafny.types.GetExtendableResourceErrorsOutput.default())()
        d_74_obj_: object
        nw1_ = ExtendableResource_Compile.OpaqueMessage()
        nw1_.ctor__()
        d_74_obj_ = nw1_
        output = Wrappers_Compile.Result_Failure(simple.extendable.resources.internaldafny.types.Error_Opaque(d_74_obj_))
        return output
        return output

    @property
    def name(self):
        return self._name

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "ExtendableResource_Compile._default"
    @_dafny.classproperty
    def DEFAULT__RESOURCE__NAME(instance):
        return _dafny.Seq("dafny-default")
