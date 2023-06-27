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
import simple.errors.internaldafny.types
import SimpleErrorsImpl_Compile
import simple.errors.internaldafny.impl

assert "simple.errors.internaldafny.wrapped" == __name__

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "simple.errors.internaldafny.wrapped_Compile._default"
    @staticmethod
    def WrappedDefaultSimpleErrorsConfig():
        return simple.errors.internaldafny.types.SimpleErrorsConfig_SimpleErrorsConfig()

