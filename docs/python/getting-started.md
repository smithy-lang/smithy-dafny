# Getting Started

To install dependencies to build a Smithy-Dafny project in Python, first run

```
make setup_python
```

# Makefile Variables

To build a Smithy-Dafny Python project, you will need to add the following variables to your Makefile.

- `PYTHON_MODULE_NAME`: The name of the Python module for generated code.
- `TRANSLATION_RECORD_PYTHON` : For each dependency (including StandardLibrary), the path to the generated `.dtr` file for that dependency’s generated Dafny code.
- `PYTHON_DEPENDENCY_MODULE_NAMES`: For each dependency, this is a map from a Smithy namespace to the `PYTHON_MODULE_NAME` variable for that dependency.

Examples:

- [Crypto Tools’ MPL](https://github.com/aws/aws-cryptographic-material-providers-library/blob/main/AwsCryptographicMaterialProviders/Makefile). This project sets all of these variables with multiple dependencies.

### Smithy-Dafny Python Project Structure

(Assuming you have made the Makefile updates specified above, then:)

These commands will set up the base file structure for a Python project:

1. `make polymorph_dafny`
2. `make polymorph_python`
3. `make transpile_python`

This structure follows:

```
MyProject/runtimes/python/
├── src/
│   └── my_project/
│       ├── __init__.py
│       ├── internaldafny/
│       │   ├── generated/
│       │   │   ├── [all Dafny-generated source code from `make transpile_python`]
│       │   │   └── dafny_src-py.dtr
│       │   └── extern/
│       │       ├── __init__.py
│       │       └── [all manually written externs]
│       └── smithygenerated/
│           └── my_project/
│               └── [all Smithy-Dafny-generated source code from `make polymorph_python`]
├── test/
│   ├──  __init__.py  # empty
│   └── internaldafny/
│       ├── __init__.py  # empty
│       ├── test_dafny_wrapper.py
│       ├── generated/
│       │   ├── [all Dafny-generated test code from `make transpile_python`]
│       └── extern/
│           ├── __init__.py
│           └── [all manually test written externs]
├── pyproject.toml
├── tox.ini
└── .gitignore
```

- `src/` : Project source code.
  - `my_project/` : Python module that will be distributed to end users. This is the top-level name of the package that is imported by users. (ex. `import my_project`). The top-level name is defined by the Smithy-Dafny project’s Makefile’s `PYTHON_MODULE_NAME` variable; see [Makefile Updates](https://quip-amazon.com/SahBABLOQkya#temp:C:KIXe7b270945e2b419180867c04e).
    - `__init__.py`: Initializes generated Dafny code and performs optional project setup. See Appendix.
    - `internaldafny/`: Dafny-generated code and externs.
      - `generated/`: Dafny-generated code.
        - `dafny_src-py.dtr`: [Dafny translation record](https://dafny.org/dafny/DafnyRef/DafnyRef#sec-dtr-files) for this project’s generated code. This is critical to let other projects use this project as a dependency. Other projects will read this file to determine how to refer to this project’s generated Dafny code.
      - `extern/`: Holds manually-written externs. You don’t need this if you don’t have any source externs.
        - `__init__.py` : Initializes externs. See Appendix.
    - `smithygenerated/`: Smithy-Dafny generated code.
      - `my_project/`: Smithy-generated code for a LocalService’s namespace.
      - Note: If a Smithy-Dafny project has multiple LocalServices, there will be multiple folders in this directory. Each folder will named be the LocalService’s Smithy namespace converted to snakecase. For an example, see [Crypto Tools’ MPL](https://github.com/aws/aws-cryptographic-material-providers-library/tree/main/AwsCryptographicMaterialProviders/runtimes/python/src/aws_cryptographic_materialproviders/smithygenerated).
- `test/`: Project test code.
  - `internaldafny/`: Dafny tests.
    - `test_dafny_wrapper.py`: See Appendix.
      - `generated/` : Dafny-generated test code.
      - `extern/`: Holds manually-written test externs. You don’t need this if you don’t have any test externs.
  - Any other test groupings, ex. `functional/`: Other tests for the project that aren’t Dafny-generated. For an example, See [Crypto Tools’ AwsCryptographyPrimitives](https://github.com/aws/aws-cryptographic-material-providers-library/tree/main/AwsCryptographyPrimitives/runtimes/python/test).
- `pyproject.toml` : Project configuration and dependencies file. See Appendix.
- `tox.ini` : Test configuration file. See Appendix.

# Externs

In Python, Dafny externs are not loaded at compile time because "compile time" doesn't exist in Python. Python code is interpreted, not compiled.
Smithy-Dafny Python projects use this pattern to link extern code when the Smithy-Dafny module is loaded.

Smithy-Dafny Python extern implementations must:

1. Extend the generated class, if there is one
2. “Export” itself to the generated class
   1. **Why?** The Dafny-generated code expects that generated code behaves like it has extern code. The extern class that extends the generated class has this behavior. Overwriting the generated class with the extern class matches Dafny’s expectation.

Annotated sample implementation:

```
# If this is generated by `transpile_python`
import my_project.internaldafny.generated.ModuleWithExtern.SomeExternCLass
# Your extern might need code from the generated module
from my_project.internaldafny.generated.ModuleWithExtern import *

# Extern should extend generated class, if one is generated
class SomeExternClass(my_project.internaldafny.generated.SomeExternClass):
    ...

# Export extern class to generated class
my_project.internaldafny.generated.ModuleWithExtern.SomeExternClass = SomeExternClass
```

This extern file should be placed at `my_project/internaldafny/extern`.

Every project that has externs must also have an `__init__.py` located at `my_project/internaldafny/extern` with the code at [TODO].

Examples:

- [Extern TestModel](https://github.com/smithy-lang/smithy-dafny/tree/main-1.x/TestModels/Extern/runtimes/python/src/simple_dafnyextern/internaldafny/extern).

# Appendix

## Code Samples

### Project Initialization Files

Every Smithy-Dafny project should have a file at `src/your_project/__init__.py` with the following content:

```
# Initialize generated Dafny
from .internaldafny.generated import module_

# Initialize externs
# (If you don't have externs, omit this import)
from .internaldafny import extern
```

This file is executed when your project is imported.

This file primarily exists to initialize a project’s Dafny code.

First, this file initializes generated Dafny by importing the generated `module_.py`.
`module_.py` is a Dafny-generated file that imports a project’s generated Dafny topologically (i.e. avoiding circular dependencies in import dependencies).

Second, this file initializes externs.
(This order is important; externs rely on generated code, and the generated code must be imported first to avoid circular dependencies.)

To use externs in source code, you must add a file at `my_project/internaldafny/extern/__init__.py`.
This file is executed by the root `__init__.py` when the project is imported.
This file will import externs.

```
from . import (
    MyExtern
)
```

Examples:

- [Constraints TestModel](https://github.com/smithy-lang/smithy-dafny/blob/main-1.x/TestModels/Constraints/runtimes/python/src/simple_constraints/__init__.py). This has no externs, so the `import extern` line is omitted.
- [Extern TestModel](https://github.com/smithy-lang/smithy-dafny/tree/main-1.x/TestModels/Extern/runtimes/python/src/simple_dafnyextern). This has both generated and extern code.
