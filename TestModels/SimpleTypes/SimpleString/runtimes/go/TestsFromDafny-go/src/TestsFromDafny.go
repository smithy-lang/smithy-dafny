// Dafny program the_program compiled into Go
package main

import (
  _dafny "dafny"
  os "os"
  _System "System_"
  Wrappers "Wrappers"
  StandardLibrary_mUInt "StandardLibrary_mUInt"
  StandardLibrary "StandardLibrary"
  UTF8 "UTF8"
  simpletypessmithystringinternaldafnytypes "simpletypessmithystringinternaldafnytypes"
  SimpleStringImpl "SimpleStringImpl"
  simpletypessmithystringinternaldafny "simpletypessmithystringinternaldafny"
  simpletypessmithystringinternaldafnywrapped "simpletypessmithystringinternaldafnywrapped"
  SimpleStringImplTest "SimpleStringImplTest"
  WrappedSimpleTypesStringTest "WrappedSimpleTypesStringTest"
)
var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_mUInt.Dummy__
var _ StandardLibrary.Dummy__
var _ SimpleStringImpl.Dummy__
var _ SimpleStringImplTest.Dummy__
var _ WrappedSimpleTypesStringTest.Dummy__

// Definition of class Default__
type Default__ struct {
  dummy byte
}

func New_Default___() *Default__ {
  _this := Default__{}

  return &_this
}

type CompanionStruct_Default___ struct {
}
var Companion_Default___ = CompanionStruct_Default___ {
}

func (_this *Default__) Equals(other *Default__) bool {
  return _this == other
}

func (_this *Default__) EqualsGeneric(x interface{}) bool {
  other, ok := x.(*Default__)
  return ok && _this.Equals(other)
}

func (*Default__) String() string {
  return "_module.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) Test____Main____(__noArgsParameter _dafny.Sequence) {
  var _87_success bool
  _ = _87_success
  _87_success = true
  _dafny.Print((_dafny.SeqOfString("SimpleStringImplTest.GetString: ")).SetString())
  func() {
    defer func() {
      if r := recover(); r != nil {
        var _88_haltMessage = _dafny.SeqOfString(r.(string))
        {
          _dafny.Print((_dafny.SeqOfString("FAILED\n	")).SetString())
          _dafny.Print((_88_haltMessage).SetString())
          _dafny.Print((_dafny.SeqOfString("\n")).SetString())
          _87_success = false
        }
      }
    }()
    {
      SimpleStringImplTest.Companion_Default___.GetString()
      {
        _dafny.Print((_dafny.SeqOfString("PASSED\n")).SetString())
      }
    }
  }()
  _dafny.Print((_dafny.SeqOfString("WrappedSimpleTypesStringTest.GetString: ")).SetString())
  func() {
    defer func() {
      if r := recover(); r != nil {
        var _89_haltMessage = _dafny.SeqOfString(r.(string))
        {
          _dafny.Print((_dafny.SeqOfString("FAILED\n	")).SetString())
          _dafny.Print((_89_haltMessage).SetString())
          _dafny.Print((_dafny.SeqOfString("\n")).SetString())
          _87_success = false
        }
      }
    }()
    {
      WrappedSimpleTypesStringTest.Companion_Default___.GetString()
      {
        _dafny.Print((_dafny.SeqOfString("PASSED\n")).SetString())
      }
    }
  }()
  if (!(_87_success)) {
    panic("test/WrappedSimpleStringTest.dfy(3,0): " + (_dafny.SeqOfString("Test failures occurred: see above.\n")).String())
  }
}
// End of class Default__
func main() {
  defer _dafny.CatchHalt()
  Companion_Default___.Test____Main____(_dafny.FromMainArguments(os.Args))
}
