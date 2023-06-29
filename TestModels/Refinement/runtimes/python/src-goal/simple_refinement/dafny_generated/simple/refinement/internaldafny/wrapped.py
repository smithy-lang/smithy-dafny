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
import simple.refinement.internaldafny.types
import SimpleRefinementImpl_Compile
import simple.refinement.internaldafny.impl

assert "simple.refinement.internaldafny.wrapped" == __name__

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "simple.refinement.internaldafny.wrapped_Compile._default"
    @staticmethod
    def WrappedDefaultSimpleRefinementConfig():
        return simple.refinement.internaldafny.types.SimpleRefinementConfig_SimpleRefinementConfig()

