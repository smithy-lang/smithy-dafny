import sys

module_root_dir = '/'.join(__file__.split("/")[:-1])

sys.path.append(module_root_dir + "/internaldafny/extern")
sys.path.append(module_root_dir + "/internaldafny/generated")
sys.path.append(module_root_dir + "/smithygenerated")