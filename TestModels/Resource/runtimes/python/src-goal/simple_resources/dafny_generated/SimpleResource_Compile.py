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
import simple.resources.internaldafny.types
import Helpers_Compile

assert "SimpleResource_Compile" == __name__
SimpleResource_Compile = sys.modules[__name__]

class SimpleResource(simple.resources.internaldafny.types.ISimpleResource):
    def  __init__(self):
        print("resource_compile")
        self._value: Wrappers_Compile.Option = Wrappers_Compile.Option_None.default()()
        self._name: _dafny.Seq = _dafny.Seq({})
        pass

    def __dafnystr__(self) -> str:
        return "SimpleResource_Compile.SimpleResource"
    def GetResourceData(self, input):
        print("getting")
        out1_: Wrappers_Compile.Result
        out1_ = simple.resources.internaldafny.types.ISimpleResource.GetResourceData(self, input)
        return out1_

    def ctor__(self, value, name):
        (self)._value = value
        (self)._name = name

    def GetResourceData_k(self, input):
        output: Wrappers_Compile.Result = Wrappers_Compile.Result_Success.default(simple.resources.internaldafny.types.GetResourceDataOutput.default())()
        d_71_rtnString_: _dafny.Seq
        d_71_rtnString_ = ((((self).name) + (_dafny.Seq(" "))) + (((input).stringValue).value) if ((input).stringValue).is_Some else (self).name)
        d_72_rtn_: simple.resources.internaldafny.types.GetResourceDataOutput
        d_72_rtn_ = simple.resources.internaldafny.types.GetResourceDataOutput_GetResourceDataOutput((input).blobValue, (input).booleanValue, Wrappers_Compile.Option_Some(d_71_rtnString_), (input).integerValue, (input).longValue)
        output = Wrappers_Compile.Result_Success(d_72_rtn_)
        return output
        return output

    @property
    def value(self):
        return self._value
    @property
    def name(self):
        return self._name

