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
import simple_boolean.simple.types.boolean.internaldafny.types
import simple_boolean.SimpleBooleanImpl
import simple_boolean.simple.types.boolean.internaldafny.impl
import SimpleBooleanImplTest

assert "simple.types.boolean.internaldafny.wrapped" == __name__

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def WrappedDefaultSimpleBooleanConfig():
        return simple.types.boolean.internaldafny.types.SimpleBooleanConfig_SimpleBooleanConfig()

