# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
from simple_dafnyextern.internaldafny.generated.SimpleExternImpl import *
from simple_dafnyextern.internaldafny.generated import SimpleDafnyExternTypes
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers

@staticmethod
def GetExtern(config, input):
  out = SimpleDafnyExternTypes.GetExternOutput_GetExternOutput(
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
  return Wrappers.Result_Failure(SimpleDafnyExternTypes.Error_Opaque(exception))

default__.GetExtern = GetExtern
default__.ExternMustError = ExternMustError