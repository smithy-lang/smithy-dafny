# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0

# Initialize generated Dafny
import simple_types_boolean.internaldafny.generated.module_

# If this is the first Dafny module to load,
# set this as the main module for the DafnyRuntime package
try:
    import module_
except ImportError:
    import sys
    sys.modules["module_"] = simple_types_boolean.internaldafny.generated.module_
