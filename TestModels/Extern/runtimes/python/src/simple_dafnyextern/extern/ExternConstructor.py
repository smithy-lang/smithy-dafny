from simple_dafnyextern.internaldafny.ExternConstructor import *
import simple_dafnyextern_internaldafny_types
import Wrappers
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
        return Wrappers.Result_Failure(simple_dafnyextern_internaldafny_types.Error_Opaque(e))