"""
Wrapper file for executing Dafny tests from pytest.
This allows us to import modules required by Dafny-generated tests
before executing Dafny-generated tests.
pytest will find and execute the `test_dafny` method below,
which will execute the `__main__.py` file in the `dafny` directory.
"""

import sys

# Dafny-generated tests are not compiled as a package
# and require adding Dafny-generated test code to PYTHONPATH.
# These files are only on PYTHONPATH for tests executed from this file.

internaldafny_dir = '/'.join(__file__.split("/")[:-1])

sys.path.append(internaldafny_dir + "/extern")
sys.path.append(internaldafny_dir + "/generated")

# Initialize extern for test
from .extern import wrapped_simple_streaming

def test_dafny():
  from .generated import __main__