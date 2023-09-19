"""
Wrapper file for executing Dafny tests from pytest.
This allows us to import modules required by Dafny-generated tests
before executing Dafny-generated tests.
pytest will find and execute the `test_dafny` method below,
which will execute the `test.py` file in the `dafny` directory.
"""

import glob
from os.path import isfile, join
import importlib

# Import modules required for Dafny-generated tests.
# This is not generated; these must be manually added.

from simple_types_smithystring.extern import wrapped_simple_string

# End import modules required for Dafny-generated tests

def test_dafny():
  dafny_modules = glob.glob(join("/".join(__file__.split("/")[:-2]) + "/internal_generated_dafny/", "*.py"), recursive=True)
  for f in dafny_modules:
    if isfile(f) and f.endswith('test.py'):
      fname = str(f).split("/")[-1].split(".")[0]
      spec = importlib.util.spec_from_file_location(fname, f)
      module = importlib.util.module_from_spec(spec)
      spec.loader.exec_module(module)