import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import simple.types.boolean.internaldafny.types
import SimpleBooleanImpl_Compile
import simple.types.boolean.internaldafny.impl

assert "module_" == __name__
module_ = sys.modules[__name__]

