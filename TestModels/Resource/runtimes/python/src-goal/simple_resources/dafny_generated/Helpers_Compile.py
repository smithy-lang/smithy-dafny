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

assert "Helpers_Compile" == __name__
Helpers_Compile = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "Helpers_Compile._default"
    @staticmethod
    def allNone():
        return simple.resources.internaldafny.types.GetResourceDataInput_GetResourceDataInput(Wrappers_Compile.Option_None(), Wrappers_Compile.Option_None(), Wrappers_Compile.Option_None(), Wrappers_Compile.Option_None(), Wrappers_Compile.Option_None())

    @staticmethod
    def checkMostNone(name, output):
        if not((Wrappers_Compile.Option_Some(name)) == ((output).stringValue)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Resource/test/Helpers.dfy(26,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not((Wrappers_Compile.Option_None()) == ((output).blobValue)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Resource/test/Helpers.dfy(27,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not((Wrappers_Compile.Option_None()) == ((output).booleanValue)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Resource/test/Helpers.dfy(28,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not((Wrappers_Compile.Option_None()) == ((output).integerValue)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Resource/test/Helpers.dfy(29,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not((Wrappers_Compile.Option_None()) == ((output).longValue)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Resource/test/Helpers.dfy(30,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))

    @staticmethod
    def allSome():
        return simple.resources.internaldafny.types.GetResourceDataInput_GetResourceDataInput(Wrappers_Compile.Option_Some(_dafny.Seq([1])), Wrappers_Compile.Option_Some(True), Wrappers_Compile.Option_Some(_dafny.Seq("Some")), Wrappers_Compile.Option_Some(1), Wrappers_Compile.Option_Some(1))

    @staticmethod
    def checkSome(name, output):
        if not((Wrappers_Compile.Option_Some((name) + (_dafny.Seq(" Some")))) == ((output).stringValue)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Resource/test/Helpers.dfy(49,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not((Wrappers_Compile.Option_Some(_dafny.Seq([1]))) == ((output).blobValue)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Resource/test/Helpers.dfy(50,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not((Wrappers_Compile.Option_Some(True)) == ((output).booleanValue)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Resource/test/Helpers.dfy(51,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not((Wrappers_Compile.Option_Some(1)) == ((output).integerValue)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Resource/test/Helpers.dfy(52,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))
        if not((Wrappers_Compile.Option_Some(1)) == ((output).longValue)):
            raise _dafny.HaltException("/Users/lucmcdon/Desktop/workplace/polymorph/TestModels/Resource/test/Helpers.dfy(53,4): " + _dafny.string_of(_dafny.Seq("expectation violation")))

