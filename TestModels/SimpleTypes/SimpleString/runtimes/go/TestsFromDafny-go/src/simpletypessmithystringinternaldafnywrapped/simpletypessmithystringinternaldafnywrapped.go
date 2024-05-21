// Package simpletypessmithystringinternaldafnywrapped
// Dafny module simpletypessmithystringinternaldafnywrapped compiled into Go

package simpletypessmithystringinternaldafnywrapped

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
)
var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_mUInt.Dummy__
var _ StandardLibrary.Dummy__
var _ SimpleStringImpl.Dummy__

type Dummy__ struct{}


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
  return "simpletypessmithystringinternaldafnywrapped.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) WrappedDefaultSimpleStringConfig() simpletypessmithystringinternaldafnytypes.SimpleStringConfig {
  return simpletypessmithystringinternaldafnytypes.Companion_SimpleStringConfig_.Create_SimpleStringConfig_()
}
// End of class Default__
