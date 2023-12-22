"""
Wrapper file for executing Dafny tests from pytest.
This allows us to import modules required by Dafny-generated tests
before executing Dafny-generated tests.
pytest will find and execute the `test_dafny` method below,
which will execute the `internaldafny_test_executor.py` file in the `dafny` directory.
"""

# TODO-Python: Remove PYTHONPATH workaround, use fully-qualified module names via dfyproject.toml.
import sys

internaldafny_dir = '/'.join(__file__.split("/")[:-1])

sys.path.append(internaldafny_dir + "/extern")
sys.path.append(internaldafny_dir + "/generated")

# Import modules required for Dafny-generated tests.
# This is not generated; these must be manually added.
# This can be removed once PYTHONPATH workaround is removed,
# and all Dafny-generated imports are fully qualified.

import simple_aggregate

# End import modules required for Dafny-generated tests

def test_dafny():
  # Dafny tests are executed when importing `internaldafny_test_executor`
  import internaldafny_test_executor