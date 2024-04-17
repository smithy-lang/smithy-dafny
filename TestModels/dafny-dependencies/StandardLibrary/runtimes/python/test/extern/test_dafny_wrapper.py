# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
"""
Wrapper file for executing Dafny tests from pytest.
This allows us to import modules required by Dafny-generated tests
before executing Dafny-generated tests.
pytest will find and execute the `test_dafny` method below,
which will execute the `internaldafny_test_executor.py` file in the `dafny` directory.
"""

# Import modules required for Dafny-generated tests.
# This is not generated; these must be manually added.

# End import modules required for Dafny-generated tests

def test_dafny():
  # Dafny tests are executed when importing `internaldafny_test_executor`
  import internaldafny_test_executor