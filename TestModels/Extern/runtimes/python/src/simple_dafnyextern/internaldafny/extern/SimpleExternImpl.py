# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
from simple_dafnyextern.internaldafny.generated.SimpleExternImpl import *
import simple_dafnyextern_internaldafny_types
import standard_library.internaldafny.generated.Wrappers as Wrappers

@staticmethod
def GetExtern(config, input):
  out = simple_dafnyextern_internaldafny_types.GetExternOutput_GetExternOutput(
      blobValue = input.blobValue,
      booleanValue = input.booleanValue,
      stringValue = input.stringValue,
      integerValue = input.integerValue,
      longValue = input.longValue
  )
  return Wrappers.Result_Success(out)

@staticmethod
def ExternMustError(config, input):
  exception = Exception(input)
  return Wrappers.Result_Failure(simple_dafnyextern_internaldafny_types.Error_Opaque(exception))

default__.GetExtern = GetExtern
default__.ExternMustError = ExternMustError