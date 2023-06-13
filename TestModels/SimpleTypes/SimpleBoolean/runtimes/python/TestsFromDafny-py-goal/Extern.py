import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

import module_
import _dafny
import System_
import SimpleBooleanImplTest_Compile
import simple.types.boolean.internaldafny.types
from python_client_codegen.simple_boolean.client import SimpleBoolean
from Shim import SimpleBooleanShim
import Wrappers_Compile

@staticmethod
def WrappedSimpleBoolean(config):
    wrapped_config = config
    impl = SimpleBoolean(wrapped_config)
    wrapped_client = SimpleBooleanShim(impl)
    return Wrappers_Compile.Result_Success(wrapped_client)

# simple.types.boolean.internaldafny.wrapped.default__.WrappedSimpleBoolean = WrappedSimpleBoolean