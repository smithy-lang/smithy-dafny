import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import Wrappers
import StandardLibrary_mUInt
import StandardLibrary
import UTF8
import simple_types_boolean_internaldafny_types
import SimpleBooleanImpl
import simple_types_boolean_internaldafny_index
import SimpleBooleanImplTest

assert "simple_types_boolean_internaldafny_wrapped" == __name__
simple_types_boolean_internaldafny_wrapped = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def WrappedDefaultSimpleBooleanConfig():
        return simple_types_boolean_internaldafny_types.SimpleBooleanConfig_SimpleBooleanConfig()

