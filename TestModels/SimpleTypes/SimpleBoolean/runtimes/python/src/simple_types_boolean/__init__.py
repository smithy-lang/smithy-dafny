# Initialize generated Dafny
from .internaldafny.generated import module_

import sys

if "module_" not in sys.modules:
  sys.modules["module_"] = module_