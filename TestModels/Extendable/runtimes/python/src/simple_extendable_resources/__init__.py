# __init__.py for a Smithy-Dafny generated Python project

# TODO-Python: Remove PYTHONPATH workaround, use fully-qualified module names via dfyproject.toml.
# Import project dependencies.
# This can be removed  (TODO-Python-PYTHONPATH: Remove)
import standard_library

# Add internaldafny and smithygenerated code to PYTHONPATH (TODO-Python-PYTHONPATH: Remove)
import sys

module_root_dir = '/'.join(__file__.split("/")[:-1])

sys.path.append(module_root_dir + "/internaldafny/extern")
sys.path.append(module_root_dir + "/internaldafny/generated")
# It would be nice if this were " + smithygenerated"
# such that the root of the module is not on PYTHONPATH,
# but if the project directory name equals the smithygenerated directory name,
# then lookups that are intended to be in the smithygenerated directory
# will instead look at the project directory and fail.
# The fix is NOT to improve this workaround,
# but instead to pass dependency module names from a dfyproject.toml file to Smithy
# so it knows the fully qualified path to access smithygenerated code.
sys.path.append(module_root_dir)

# TODO-Python-PYTHONPATH: Remove
import native_resource