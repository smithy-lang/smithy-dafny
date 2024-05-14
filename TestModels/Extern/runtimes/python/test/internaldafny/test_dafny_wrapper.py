"""
Wrapper file for executing Dafny tests from pytest.
This allows us to import modules required by Dafny-generated tests
before executing Dafny-generated tests.
pytest will find and execute the `test_dafny` method below,
which will execute the `__main__.py` file in the `dafny` directory.
"""

import sys

internaldafny_dir = '/'.join(__file__.split("/")[:-1])

sys.path.append(internaldafny_dir + "/extern")
sys.path.append(internaldafny_dir + "/generated")

from .extern import wrapped_simple_extern

def test_dafny():
  # Dafny writes Dafny tests to __main__
  from .generated import __main__