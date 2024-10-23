# Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
# SPDX-License-Identifier: Apache-2.0
import simple_dafnyextern.internaldafny.generated.ExternConstructor
from simple_dafnyextern.internaldafny.generated.ExternConstructor import *
from simple_dafnyextern.internaldafny.generated import SimpleDafnyExternTypes
import smithy_dafny_standard_library.internaldafny.generated.Wrappers as Wrappers
import _dafny

class ExternConstructorClass:

  def __init__(self, input):
    if (_dafny.string_of(input) == "Error"):
      raise Exception("Python Constructor Exception")
    self.inputVal = input

  def GetValue(self):
    return Wrappers.Result_Success(self.inputVal)

  @staticmethod
  def Build(input):
      try:
        return Wrappers.Result_Success(ExternConstructorClass(input))
      except Exception as e:
        return Wrappers.Result_Failure(SimpleDafnyExternTypes.Error_Opaque(e, repr(e)))

simple_dafnyextern.internaldafny.generated.ExternConstructor.ExternConstructorClass = ExternConstructorClass
