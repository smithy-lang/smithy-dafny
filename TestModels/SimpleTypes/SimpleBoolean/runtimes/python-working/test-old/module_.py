import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

from simple_boolean import *
import module_
import _dafny
import System_
import Wrappers
import StandardLibrary_mUInt
import StandardLibrary
import UTF8
# import simple_boolean.simple.types.boolean.internaldafny.types
import simple_boolean.SimpleBooleanImpl
# import simple.types.boolean.internaldafny.impl
import SimpleBooleanImplTest
import simple.types.boolean.internaldafny.wrapped
import WrappedSimpleTypesBooleanTest

assert "module_" == __name__
module_ = sys.modules[__name__]

