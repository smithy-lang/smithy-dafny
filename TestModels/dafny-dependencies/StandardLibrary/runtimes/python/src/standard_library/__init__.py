# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# Boilerplate code for a Python package with internal Dafny code

# Initialize generated Dafny
from .internaldafny.generated import module_

# Initialize externs
from .internaldafny.extern import *

# If this is the first Dafny module to load,
# set this as the main module for the DafnyRuntime package
try:
    import module_
except ImportError:
    import sys
    sys.modules["module_"] = module_
