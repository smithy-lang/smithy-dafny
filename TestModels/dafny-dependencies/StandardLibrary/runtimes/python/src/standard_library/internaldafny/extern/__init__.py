import os
import importlib.util

import standard_library.internaldafny.generated.module_

import sys
# input(sys.modules["module_"])


def load_modules_from_directory(directory):
    # List all .py files in the directory, excluding __init__.py if present
    for filename in os.listdir(directory):
        if filename.endswith('.py') and not filename.startswith('__'):
            # Create a module name and file path
            filepath = os.path.join(directory, filename)
            mod_name = "standard_library.internaldafny." + filename[:-3]  # Strip .py to get the module name

            # Load the module dynamically
            spec = importlib.util.spec_from_file_location(mod_name, filepath)
            module = importlib.util.module_from_spec(spec)
            spec.loader.exec_module(module)

            # Attach the module to the globals() so it can be accessed as A.mod_name
            # input(mod_name)
            sys.modules[mod_name] = module
            parent_folder = directory.split("/")[-1]
            
            sys.modules[mod_name + "." + parent_folder] = module

            # input(mod_name)
            # input(sys.modules[mod_name])
            # input(mod_name + "." + parent_folder)
            # input(sys.modules[mod_name + "." + parent_folder])

# Assuming 'B' is a subdirectory of the directory containing this __init__.py
current_dir = os.path.dirname(__file__)
# input(current_dir)
load_modules_from_directory(current_dir)
# input(sys.modules["standard_library.internaldafny.Time"])
# input(sys.modules["standard_library.internaldafny.generated.Time"])
# b_dir = os.path.join(current_dir, 'extern')
# load_modules_from_directory(b_dir)
