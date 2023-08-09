import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

# from . import module_
from . import _dafny
from . import System_
from . import Wrappers
from . import StandardLibrary_mUInt
from . import StandardLibrary
from . import UTF8
from . import simple_types_boolean_internaldafny_types
from . import SimpleBooleanImpl
from . import simple_types_boolean_internaldafny_impl

# assert "module_" == __name__
module_ = sys.modules[__name__]

