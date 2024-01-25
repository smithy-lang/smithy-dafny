import sys

# TODO-Python: Remove PYTHONPATH workaround, use fully-qualified module names via dfyproject.toml.
module_root_dir = '/'.join(__file__.split("/")[:-1])

sys.path.append(module_root_dir + "/internaldafny/extern")
sys.path.append(module_root_dir + "/internaldafny/generated")