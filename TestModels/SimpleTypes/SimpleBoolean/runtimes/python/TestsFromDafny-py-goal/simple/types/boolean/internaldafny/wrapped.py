import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import SimpleBooleanImplTest_Compile
import simple.types.boolean.internaldafny.types

assert "simple.types.boolean.internaldafny.wrapped" == __name__

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "simple.types.boolean.internaldafny.wrapped_Compile._default"
    @staticmethod
    def WrappedDefaultSimpleBooleanConfig():
        return simple.types.boolean.internaldafny.types.SimpleBooleanConfig_SimpleBooleanConfig()

