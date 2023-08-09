import sys
from typing import Callable, Any, TypeVar, NamedTuple
from math import floor
from itertools import count

# from . import module_
from . import _dafny

# assert "System_" == __name__
System_ = sys.modules[__name__]

class nat:
    def  __init__(self):
        pass

    @staticmethod
    def default():
        return int(0)
