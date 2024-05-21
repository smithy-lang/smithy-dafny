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
  simple.constraints.internaldafny.types "simple.constraints.internaldafny.types"
  SimpleConstraintsImpl "SimpleConstraintsImpl"
  simpleconstraintsinternaldafny "simpleconstraintsinternaldafny"
  simpleconstraintsinternaldafnywrapped "simpleconstraintsinternaldafnywrapped"
  Helpers "Helpers"
  SimpleConstraintsImplTest "SimpleConstraintsImplTest"
  WrappedSimpleConstraintsTest "WrappedSimpleConstraintsTest"
)
var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_mUInt.Dummy__
var _ StandardLibrary.Dummy__
var _ SimpleConstraintsImpl.Dummy__
var _ Helpers.Dummy__
var _ SimpleConstraintsImplTest.Dummy__
var _ WrappedSimpleConstraintsTest.Dummy__

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
  var _114_success bool
  _ = _114_success
  _114_success = true
  _dafny.Print((_dafny.SeqOfString("SimpleConstraintsImplTest.TestConstraints: ")).SetString())
  func() {
    defer func() {
      if r := recover(); r != nil {
        var _115_haltMessage = _dafny.SeqOfString(r.(string))
        {
          _dafny.Print((_dafny.SeqOfString("FAILED\n	")).SetString())
          _dafny.Print((_115_haltMessage).SetString())
          _dafny.Print((_dafny.SeqOfString("\n")).SetString())
          _114_success = false
        }
      }
    }()
    {
      SimpleConstraintsImplTest.Companion_Default___.TestConstraints()
      {
        _dafny.Print((_dafny.SeqOfString("PASSED\n")).SetString())
      }
    }
  }()
  _dafny.Print((_dafny.SeqOfString("WrappedSimpleConstraintsTest.GetConstraints: ")).SetString())
  func() {
    defer func() {
      if r := recover(); r != nil {
        var _116_haltMessage = _dafny.SeqOfString(r.(string))
        {
          _dafny.Print((_dafny.SeqOfString("FAILED\n	")).SetString())
          _dafny.Print((_116_haltMessage).SetString())
          _dafny.Print((_dafny.SeqOfString("\n")).SetString())
          _114_success = false
        }
      }
    }()
    {
      WrappedSimpleConstraintsTest.Companion_Default___.GetConstraints()
      {
        _dafny.Print((_dafny.SeqOfString("PASSED\n")).SetString())
      }
    }
  }()
  if (!(_114_success)) {
    panic("test/WrappedSimpleConstraintsTest.dfy(3,0): " + (_dafny.SeqOfString("Test failures occurred: see above.\n")).String())
  }
}
// End of class Default__
func main() {
  defer _dafny.CatchHalt()
  Companion_Default___.Test____Main____(_dafny.FromMainArguments(os.Args))
}
