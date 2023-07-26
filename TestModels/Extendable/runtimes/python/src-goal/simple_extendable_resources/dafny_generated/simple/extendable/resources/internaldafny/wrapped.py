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
import TestHelpers_Compile
import SimpleExtendableResourcesOperations_Compile
import simple.extendable.resources.internaldafny.impl
import simple.extendable.resources.internaldafny.nativeresourcefactory
import SimpleExtendableResourcesTest_Compile

assert "simple.extendable.resources.internaldafny.wrapped" == __name__

class default__:
    def  __init__(self):
        pass

    def __dafnystr__(self) -> str:
        return "simple.extendable.resources.internaldafny.wrapped_Compile._default"
    @staticmethod
    def WrappedDefaultSimpleExtendableResourcesConfig():
        return simple.extendable.resources.internaldafny.types.SimpleExtendableResourcesConfig_SimpleExtendableResourcesConfig()

