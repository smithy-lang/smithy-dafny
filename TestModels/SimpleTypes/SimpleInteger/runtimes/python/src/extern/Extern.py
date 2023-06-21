import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

from smithy_generated.simple_integer.client import SimpleInteger
from .Shim import SimpleIntegerShim
import Wrappers_Compile

@staticmethod
def WrappedSimpleInteger(config):
    wrapped_config = config
    impl = SimpleInteger(wrapped_config)
    wrapped_client = SimpleIntegerShim(impl)
    return Wrappers_Compile.Result_Success(wrapped_client)

simple.types.integer.internaldafny.wrapped.default__.WrappedSimpleInteger = WrappedSimpleInteger