import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import Dafny.Simpletypes.Boolean.Types
import SimpleBooleanImpl_Compile
import Dafny.Simpletypes.Boolean

assert "module_" == __name__
module_ = sys.modules[__name__]

