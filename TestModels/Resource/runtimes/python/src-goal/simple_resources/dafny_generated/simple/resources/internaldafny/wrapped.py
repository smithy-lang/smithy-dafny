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
import SimpleResource_Compile
import SimpleResourcesOperations_Compile
import simple.resources.internaldafny.impl
import SimpleResourcesTest_Compile

assert "simple.resources.internaldafny.wrapped" == __name__

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "simple.resources.internaldafny.wrapped_Compile._default"
    @staticmethod
    def WrappedDefaultSimpleResourcesConfig():
        return simple.resources.internaldafny.impl.default__.DefaultSimpleResourcesConfig()

