"""
Wrapper file for executing Dafny tests from pytest.
This allows us to import modules required by Dafny-generated tests
before executing Dafny-generated tests.
pytest will find and execute the `test_dafny` method below,
which will execute the `internaldafny_test_executor.py` file in the `dafny` directory.
"""

import glob
from os.path import isfile, join
import importlib

# Import modules required for Dafny-generated tests.
# This is not generated; these must be manually added.

from simple_types_smithylong.extern import wrapped_simple_long

# End import modules required for Dafny-generated tests

def test_dafny():
  # Dafny tests are executed when importing `internaldafny_test_executor`
  import __main__