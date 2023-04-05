import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import SimpleBooleanImplTest_Compile
import Dafny.Simpletypes.Boolean.Types


class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "Dafny.Simpletypes.Boolean.Wrapped_Compile._default"
    @staticmethod
    def WrappedDefaultSimpleBooleanConfig():
        return Dafny.Simpletypes.Boolean.Types.SimpleBooleanConfig_SimpleBooleanConfig()

