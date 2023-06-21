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
import simple.types.integer.internaldafny.types
import SimpleIntegerImpl_Compile
import simple.types.integer.internaldafny.impl

assert "simple.types.integer.internaldafny.wrapped" == __name__

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "simple.types.integer.internaldafny.wrapped_Compile._default"
    @staticmethod
    def WrappedDefaultSimpleIntegerConfig():
        return simple.types.integer.internaldafny.types.SimpleIntegerConfig_SimpleIntegerConfig()

