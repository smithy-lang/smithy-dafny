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
import simple_constraints_internaldafny_types
import simple_extendable_resources_internaldafny_types
import simple_resources_internaldafny_types
import simple_dependencies_internaldafny_types
import ExtendableResource
import SimpleResource
import SimpleResourcesOperations
import simple_resources_internaldafny
import SimpleDependenciesImpl
import SimpleConstraintsImpl
import simple_constraints_internaldafny
import simple_dependencies_internaldafny

assert "simple_dependencies_internaldafny_wrapped" == __name__
simple_dependencies_internaldafny_wrapped = sys.modules[__name__]

class default__:
    def  __init__(self):
        pass

    @staticmethod
    def WrappedDefaultSimpleDependenciesConfig():
        return simple_dependencies_internaldafny_types.SimpleDependenciesConfig_SimpleDependenciesConfig(Wrappers.Option_Some(simple_resources_internaldafny_types.SimpleResourcesConfig_SimpleResourcesConfig(_dafny.Seq("default"))), Wrappers.Option_None(), Wrappers.Option_None(), Wrappers.Option_Some(_dafny.Seq("bw1and10")))

