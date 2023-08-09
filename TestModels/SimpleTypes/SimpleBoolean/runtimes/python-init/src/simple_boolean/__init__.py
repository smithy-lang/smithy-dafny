import os

from os.path import dirname, basename, isfile, join
import glob
import sys
import importlib

dafny_modules = glob.glob(join("/".join(__file__.split("/")[:-1]) + "/dafny/**/", "*.py"), recursive=True)
extern_modules = glob.glob(join("/".join(__file__.split("/")[:-1]) + "/extern/**/", "*.py"), recursive=True)

print(join("/".join(__file__.split("/")[:-1])))
print("dafny_modules")
print(dafny_modules)
print("extern")
print(extern_modules)

def install_modules(modules):
  for f in modules:
    # load the module root
    if isfile(f) and  f.endswith('wrapped_simple_boolean.py'):
      sys.path.append("/".join(f.split("/")[:-1]))
      fname = str(f).split("/")[-1].split(".")[0]
      spec = importlib.util.spec_from_file_location(fname, f)
      module = importlib.util.module_from_spec(spec)
      spec.loader.exec_module(module)
  for f in modules:
    # export modules
    if isfile(f) and not f.endswith('wrapped_simple_boolean.py'):
      fname = str(f).split("/")[-1].split(".")[0]
      spec = importlib.util.spec_from_file_location(fname, f)
      module = importlib.util.module_from_spec(spec)
      sys.modules[fname] = module
      # spec.loader.exec_module(module)
  # load the module root


def execute_modules(modules):
  for f in modules:
    if isfile(f):
      sys.path.append("/".join(f.split("/")[:-1]))
      fname = str(f).split("/")[-1].split(".")[0]
      spec = importlib.util.spec_from_file_location(fname, f)
      module = importlib.util.module_from_spec(spec)
      spec.loader.exec_module(module)


install_modules(dafny_modules)
install_modules(extern_modules)
execute_modules(extern_modules)
execute_modules(dafny_modules)


#
# modules_test = glob.glob(join("/".join(__file__.split("/")[:-1]) + "/dafny/**/", "*.py"), recursive=True)
#
# for f in modules_test:
#   if isfile(f) and  f.endswith('wrapped_simple_boolean.py'):
#     sys.path.append("/".join(f.split("/")[:-1]))
#     fname = str(f).split("/")[-1].split(".")[0]
#     spec = importlib.util.spec_from_file_location(fname, f)
#     module = importlib.util.module_from_spec(spec)
#     spec.loader.exec_module(module)
# for f in modules_test:
#   if isfile(f) and not f.endswith('wrapped_simple_boolean.py') and not f.endswith('test.py'):
#     print(f)
#     fname = str(f).split("/")[-1].split(".")[0]
#     spec = importlib.util.spec_from_file_location(fname, f)
#     print("spec")
#     print(spec)
#     module = importlib.util.module_from_spec(spec)
#     print("module")
#     print(module)
#     print(module.__dict__)
#     try:
#       sys.modules[fname].__dict__.update(module.__dict__)
#     except KeyError:
#       sys.modules[fname] = module
#     spec.loader.exec_module(module)
#     print(module.__dict__)
#
# modulesExtern = glob.glob(join("/".join(__file__.split("/")[:-2]) + "/src/**/extern/**/", "*.py"), recursive=True)
#
# for f in modulesExtern:
#   if isfile(f) and  f.endswith('wrapped_simple_boolean.py'):
#     sys.path.append("/".join(f.split("/")[:-1]))
#     fname = str(f).split("/")[-1].split(".")[0]
#     spec = importlib.util.spec_from_file_location(fname, f)
#     module = importlib.util.module_from_spec(spec)
#     spec.loader.exec_module(module)
# for f in modulesExtern:
#   if isfile(f) and not f.endswith('wrapped_simple_boolean.py'):
#     print(f)
#     fname = str(f).split("/")[-1].split(".")[0]
#     spec = importlib.util.spec_from_file_location(fname, f)
#     print("spec")
#     print(spec)
#     module = importlib.util.module_from_spec(spec)
#     print("module")
#     print(module)
#     print(module.__dict__)
#     sys.modules[fname] = module
#     spec.loader.exec_module(module)
#     print(module.__dict__)
#
# print(sys.modules)
#
# from math import floor
# from itertools import count
#
# import module_
# import _dafny
#
# print(_dafny)
# print(_dafny.__dict__)
#
# from dafny import module_
#
#
# print(_dafny)
# print(_dafny.__dict__)
#
# try:
#   dafnyArgs = [_dafny.Seq(a) for a in sys.argv]
#   module_.default__.Test____Main____(dafnyArgs)
# except _dafny.HaltException as e:
#   _dafny.print("[Program halted] " + e.message + "\n")
#   sys.exit(1)


# import importlib
# import pkgutil
# import os
#
# print(__file__)
# print(__name__)
# print("/".join(__file__.split("/")[:-2]) + "/src")
# modules = pkgutil.iter_modules(["/".join(__file__.split("/")[:-2]) + "/src"])
# print("hi????")
# for mod in modules:
#   print(mod)
#   print("ok")
#
# print("here")
# print(modules)
#
#
# for mod_info in pkgutil.iter_modules(["/".join(__file__.split("/")[:-2]) + "/src"]):
#   print(mod_info)
#   print("umm?")
#   print(mod_info.name)
#   mod = importlib.import_module(mod_info.name)
#
#   # Emulate `from mod import *`
#   try:
#     print('eyo')
#     names = mod.__dict__['__all__']
#     print("yo")
#     print(names)
#   except KeyError:
#     print("nope")
#     names = [k for k in mod.__dict__ if not k.startswith('_')]
#     print(names)
#
#   globals().update({k: getattr(mod, k) for k in names})
#   for name in names:
#     print(name)
#     # sys.modules[name] =y"])

# import os
#
# from os.path import dirname, basename, isfile, join
# import glob
# print(join("/".join(__file__.split("/")[:-2]) + "/src"))
# modules = glob.glob(join("/".join(__file__.split("/")[:-2]) + "/src/**/dafny/**/", "*.py"), recursive=True)
# print(modules)
# modules2 = glob.glob(join("/".join(__file__.split("/")[:-2]) + "/src/smithy", "*.py"), recursive=True)
# print(modules2)
# # __all__ = [ basename(f)[:-3] for f in modules if isfile(f) and f.endswith('wrapped_simple_boolean.py')]
#
# import sys
# import importlib
# for f in modules:
#   if isfile(f) and  f.endswith('wrapped_simple_boolean.py'):
#     sys.path.append("/".join(f.split("/")[:-1]))
#     fname = str(f).split("/")[-1].split(".")[0]
#     spec = importlib.util.spec_from_file_location(fname, f)
#     module = importlib.util.module_from_spec(spec)
#     spec.loader.exec_module(module)
# for f in modules:
#   if isfile(f) and not f.endswith('wrapped_simple_boolean.py'):
#     print(f)
#     fname = str(f).split("/")[-1].split(".")[0]
#     spec = importlib.util.spec_from_file_location(fname, f)
#     print("spec")
#     print(spec)
#     module = importlib.util.module_from_spec(spec)
#     print("module")
#     print(module)
#     print(module.__dict__)
#     sys.modules[fname] = module
#     spec.loader.exec_module(module)
#     print(module.__dict__)
#
#
# modules_test = glob.glob(join("/".join(__file__.split("/")[:-1]) + "/dafny/**/", "*.py"), recursive=True)
#
# for f in modules_test:
#   if isfile(f) and  f.endswith('wrapped_simple_boolean.py'):
#     sys.path.append("/".join(f.split("/")[:-1]))
#     fname = str(f).split("/")[-1].split(".")[0]
#     spec = importlib.util.spec_from_file_location(fname, f)
#     module = importlib.util.module_from_spec(spec)
#     spec.loader.exec_module(module)
# for f in modules_test:
#   if isfile(f) and not f.endswith('wrapped_simple_boolean.py') and not f.endswith('test.py'):
#     print(f)
#     fname = str(f).split("/")[-1].split(".")[0]
#     spec = importlib.util.spec_from_file_location(fname, f)
#     print("spec")
#     print(spec)
#     module = importlib.util.module_from_spec(spec)
#     print("module")
#     print(module)
#     print(module.__dict__)
#     try:
#       sys.modules[fname].__dict__.update(module.__dict__)
#     except KeyError:
#       sys.modules[fname] = module
#     spec.loader.exec_module(module)
#     print(module.__dict__)
#
# modulesExtern = glob.glob(join("/".join(__file__.split("/")[:-2]) + "/src/**/extern/**/", "*.py"), recursive=True)
#
# for f in modulesExtern:
#   if isfile(f) and  f.endswith('wrapped_simple_boolean.py'):
#     sys.path.append("/".join(f.split("/")[:-1]))
#     fname = str(f).split("/")[-1].split(".")[0]
#     spec = importlib.util.spec_from_file_location(fname, f)
#     module = importlib.util.module_from_spec(spec)
#     spec.loader.exec_module(module)
# for f in modulesExtern:
#   if isfile(f) and not f.endswith('wrapped_simple_boolean.py'):
#     print(f)
#     fname = str(f).split("/")[-1].split(".")[0]
#     spec = importlib.util.spec_from_file_location(fname, f)
#     print("spec")
#     print(spec)
#     module = importlib.util.module_from_spec(spec)
#     print("module")
#     print(module)
#     print(module.__dict__)
#     sys.modules[fname] = module
#     spec.loader.exec_module(module)
#     print(module.__dict__)
#
# print(sys.modules)
#
# from math import floor
# from itertools import count
#
# import module_
# import _dafny
#
# print(_dafny)
# print(_dafny.__dict__)
#
# from dafny import module_
#
#
# print(_dafny)
# print(_dafny.__dict__)
#
# try:
#   dafnyArgs = [_dafny.Seq(a) for a in sys.argv]
#   module_.default__.Test____Main____(dafnyArgs)
# except _dafny.HaltException as e:
#   _dafny.print("[Program halted] " + e.message + "\n")
#   sys.exit(1)
#
#
# # import importlib
# # import pkgutil
# # import os
# #
# # print(__file__)
# # print(__name__)
# # print("/".join(__file__.split("/")[:-2]) + "/src")
# # modules = pkgutil.iter_modules(["/".join(__file__.split("/")[:-2]) + "/src"])
# # print("hi????")
# # for mod in modules:
# #   print(mod)
# #   print("ok")
# #
# # print("here")
# # print(modules)
# #
# #
# # for mod_info in pkgutil.iter_modules(["/".join(__file__.split("/")[:-2]) + "/src"]):
# #   print(mod_info)
# #   print("umm?")
# #   print(mod_info.name)
# #   mod = importlib.import_module(mod_info.name)
# #
# #   # Emulate `from mod import *`
# #   try:
# #     print('eyo')
# #     names = mod.__dict__['__all__']
# #     print("yo")
# #     print(names)
# #   except KeyError:
# #     print("nope")
# #     names = [k for k in mod.__dict__ if not k.startswith('_')]
# #     print(names)
# #
# #   globals().update({k: getattr(mod, k) for k in names})
# #   for name in names:
# #     print(name)
# #     # sys.modules[name] =y"])