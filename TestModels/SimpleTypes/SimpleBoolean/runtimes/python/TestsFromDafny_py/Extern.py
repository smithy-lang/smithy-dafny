import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import SimpleBooleanImplTest_Compile
import Dafny.Simpletypes.Boolean.Types
from simple_boolean.client import SimpleBoolean
from Shim import SimpleBooleanShim
import Wrappers_Compile

@staticmethod
def WrappedSimpleBoolean(config):
    wrapped_config = config
    impl = SimpleBoolean(wrapped_config)
    wrapped_client = SimpleBooleanShim(impl)
    return Wrappers_Compile.Result_Success(wrapped_client)

Dafny.Simpletypes.Boolean.Wrapped.default__.WrappedSimpleBoolean = WrappedSimpleBoolean