# __init__.py for a Smithy-Dafny generated Python project

# Add internaldafny and smithygenerated code to PYTHONPATH (TODO-Python-PYTHONPATH: Remove)
import sys

module_root_dir = '/'.join(__file__.split("/")[:-1])

sys.path.append(module_root_dir + "/internaldafny/extern")
sys.path.append(module_root_dir + "/internaldafny/generated")


# TODO-Python: Remove PYTHONPATH workaround, use fully-qualified module names via dfyproject.toml.
# Import project dependencies IN ORDER THEY MUST BE LOADED.
import standard_library
import simple_errors
import simple_resources
import simple_constraints
import simple_extendable_resources
