# # Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# # SPDX-License-Identifier: Apache-2.0
# from pathlib import Path

# from standard_library.internaldafny.generated.DafnyLibraries import *
# import standard_library.internaldafny.generated.DafnyLibraries
# import _dafny

# class MutableMap(standard_library.internaldafny.generated.DafnyLibraries.MutableMap):
#     def __init__(self):
#         super().__init__()
#         self.m = {}

#     def content(self):
#         return _dafny.Map(self.m)
    
#     def Put(self, k, v):
#         self.m[k] = v

#     def Keys(self):
#         return _dafny.Set(self.m.keys())
    
#     def HasKey(self, k):
#         return k in self.m
    
#     def Values(self):
#         return _dafny.Set(self.m.values())
    
#     def Items(self):
#         return _dafny.Set(self.m.items())
    
#     def Select(self, k):
#         return self.m[k]
    
#     def Remove(self, k):
#         del self.m[k]

#     def Size(self):
#         return len(self.m)

# class FileIO:
#     @staticmethod
#     def INTERNAL_WriteBytesToFile(dafny_path, dafny_bytes):
#         try:
#             native_path = FileIO.dafny_string_to_path(dafny_path)
#             print(f"write {native_path =}")
#             FileIO.create_parent_dirs(native_path)
#             native_bytes = bytes(dafny_bytes.Elements)
#             native_path.write_bytes(native_bytes)
#             return False, _dafny.Seq([])
#         except Exception as e:
#             return True, _dafny.Seq(str(e))
        
#     @staticmethod
#     def INTERNAL_ReadBytesFromFile(dafny_path):
#         try:
#             native_path = FileIO.dafny_string_to_path(dafny_path)
#             print(f"read {native_path =}")
#             native_bytes = native_path.read_bytes()
#             dafny_bytes = _dafny.Seq(native_bytes)
#             return False, dafny_bytes, _dafny.Seq([])
#         except Exception as e:
#             return True, _dafny.Seq([]), _dafny.Seq(str(e))

#     @staticmethod
#     def dafny_string_to_path(path_as_dafny_string):
#         return Path("../../" + _dafny.string_of(path_as_dafny_string))
    
#     @staticmethod
#     def create_parent_dirs(native_path):
#         parent = native_path.parent
#         parent_path = Path(parent)
#         parent_path.mkdir(parents=True, exist_ok=True)

# standard_library.internaldafny.generated.DafnyLibraries.FileIO = FileIO
# standard_library.internaldafny.generated.DafnyLibraries.MutableMap = MutableMap