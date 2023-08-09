# import importlib
# import pkgutil
# import os
#
# print(__file__)
# print(__name__)
# for mod_info in pkgutil.walk_packages("/".join(__file__.split("/")[:-1]), __name__ + '.'):
#   print(mod_info)
#   mod = importlib.import_module(mod_info.name)
#
#   # Emulate `from mod import *`
#   try:
#     names = mod.__dict__['__all__']
#   except KeyError:
#     names = [k for k in mod.__dict__ if not k.startswith('_')]
#
#   globals().update({k: getattr(mod, k) for k in names})
#   for name in names:
#     print(name)
#     # sys.modules[name] =
