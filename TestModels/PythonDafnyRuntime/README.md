Temporary directory containing the Python Dafny Runtime.
This lets Python projects depend on this module in their pyproject.toml.
This will be removed once Dafny uploads the Python runtime to PyPI.
Once this is on PyPI, we can update every pyproject.toml to point to PyPI and remove this folder.