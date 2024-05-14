"""
Wrapper file for executing Dafny tests from pytest.
This allows us to import modules required by Dafny-generated tests
before executing Dafny-generated tests.
pytest will find and execute the `test_dafny` method below,
which will execute the `__main__.py` file in the `dafny` directory.
"""

# TODO-Python-PYTHONPATH: Remove all sys.path.append logic from this file
import sys

internaldafny_dir = '/'.join(__file__.split("/")[:-1])

sys.path.append(internaldafny_dir + "/extern")
sys.path.append(internaldafny_dir + "/generated")

# Import modules required for Dafny-generated tests.
# This is not generated; these must be manually added.
# These are only imported to populate the PYTHONPATH.
# This can be removed once PYTHONPATH workaround is removed,
# and all Dafny-generated imports are fully qualified.
# TODO-Python-PYTHONPATH: Remove imports to initialize modules' PYTHONPATHs from this file
import standard_library
import com_amazonaws_kms

def test_dafny():
  # Dafny tests are executed when importing `internaldafny_test_executor`
  # TODO-Python-PYTHONPATH: Qualify import
  import internaldafny_test_executor