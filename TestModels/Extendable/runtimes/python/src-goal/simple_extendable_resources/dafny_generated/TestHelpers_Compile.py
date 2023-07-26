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
import ExtendableResource_Compile

assert "TestHelpers_Compile" == __name__
TestHelpers_Compile = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "TestHelpers_Compile._default"
    @staticmethod
    def allNone():
        return simple.extendable.resources.internaldafny.types.GetExtendableResourceDataInput_GetExtendableResourceDataInput(Wrappers_Compile.Option_None(), Wrappers_Compile.Option_None(), Wrappers_Compile.Option_None(), Wrappers_Compile.Option_None(), Wrappers_Compile.Option_None())

    @staticmethod
    def checkNone(output, name):
        if not(((output).stringValue) == (Wrappers_Compile.Option_Some(name))):
            print("oopsie")
            print((output).stringValue)
            print(Wrappers_Compile.Option_Some(name))
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/Helpers.dfy(27,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not(((output).blobValue).is_None):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/Helpers.dfy(28,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not(((output).booleanValue).is_None):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/Helpers.dfy(29,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not(((output).integerValue).is_None):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/Helpers.dfy(30,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not(((output).longValue).is_None):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/Helpers.dfy(31,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))

    @staticmethod
    def allSome():
        return simple.extendable.resources.internaldafny.types.GetExtendableResourceDataInput_GetExtendableResourceDataInput(Wrappers_Compile.Option_Some(_dafny.Seq([1])), Wrappers_Compile.Option_Some(True), Wrappers_Compile.Option_Some(_dafny.Seq("Some")), Wrappers_Compile.Option_Some(1), Wrappers_Compile.Option_Some(1))

    @staticmethod
    def checkSome(output, name):
        if not((Wrappers_Compile.Option_Some(((_dafny.Seq("Some")) + (_dafny.Seq(" "))) + (name))) == ((output).stringValue)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/Helpers.dfy(50,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not((Wrappers_Compile.Option_Some(_dafny.Seq([1]))) == ((output).blobValue)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/Helpers.dfy(51,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not((Wrappers_Compile.Option_Some(True)) == ((output).booleanValue)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/Helpers.dfy(52,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not((Wrappers_Compile.Option_Some(1)) == ((output).integerValue)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/Helpers.dfy(53,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not((Wrappers_Compile.Option_Some(1)) == ((output).longValue)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/Helpers.dfy(54,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))

    @staticmethod
    def CheckModeledError(errorOutput):
        print("errorOutput")
        print(errorOutput)
        if not((errorOutput).is_Failure):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/Helpers.dfy(61,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        d_75_actualError_: simple.extendable.resources.internaldafny.types.Error
        d_75_actualError_ = (errorOutput).error
        print("d_75_actualError_")
        print(d_75_actualError_)
        if not((d_75_actualError_) == (simple.extendable.resources.internaldafny.types.Error_SimpleExtendableResourcesException(_dafny.Seq("Hard Coded Exception in src/dafny")))):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/Helpers.dfy(63,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))

    @staticmethod
    def CheckMultipleErrors(errorOutput):
        if not((errorOutput).is_Failure):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/Helpers.dfy(72,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        d_76_actualError_: simple.extendable.resources.internaldafny.types.Error
        d_76_actualError_ = ((errorOutput).PropagateFailure()).error
        if not(((((d_76_actualError_).is_CollectionOfErrors) and ((len((d_76_actualError_).list)) == (1))) and ((((d_76_actualError_).list)[0]).is_SimpleExtendableResourcesException)) and (((((d_76_actualError_).list)[0]).message) == (_dafny.Seq("Hard Coded Modeled Exception in Collection")))):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/Helpers.dfy(74,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))

    @staticmethod
    def CheckOpaqueError(errorOutput):
        if not((errorOutput).is_Failure):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/Helpers.dfy(84,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        d_77_actualError_: simple.extendable.resources.internaldafny.types.Error
        d_77_actualError_ = ((errorOutput).PropagateFailure()).error
        if not((d_77_actualError_).is_Opaque):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/Helpers.dfy(86,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))

    @staticmethod
    def CheckDafnyOpaqueError(errorOutput):
        if not((errorOutput).is_Failure):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/Helpers.dfy(107,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        d_78_actualError_: simple.extendable.resources.internaldafny.types.Error
        d_78_actualError_ = ((errorOutput).PropagateFailure()).error
        def iife1_(_is_1):
            return isinstance(_is_1, ExtendableResource_Compile.OpaqueMessage)
        if not(((d_78_actualError_).is_Opaque) and (iife1_((d_78_actualError_).obj))):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Extendable/test/Helpers.dfy(109,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))

