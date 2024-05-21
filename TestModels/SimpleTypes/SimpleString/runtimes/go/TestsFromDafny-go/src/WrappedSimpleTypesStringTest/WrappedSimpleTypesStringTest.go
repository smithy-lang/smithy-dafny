// Package WrappedSimpleTypesStringTest
// Dafny module WrappedSimpleTypesStringTest compiled into Go

package WrappedSimpleTypesStringTest

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
)
var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_mUInt.Dummy__
var _ StandardLibrary.Dummy__
var _ SimpleStringImpl.Dummy__
var _ SimpleStringImplTest.Dummy__

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
  return "WrappedSimpleTypesStringTest.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) GetString() {
  var _85_client simpletypessmithystringinternaldafnytypes.ISimpleTypesStringClient
  _ = _85_client
  var _86_valueOrError0 Wrappers.Result = Wrappers.Result{}
  _ = _86_valueOrError0
  var _out7 Wrappers.Result
  _ = _out7
  _out7 = simpletypessmithystringinternaldafnywrapped.WrappedSimpleString(simpletypessmithystringinternaldafnywrapped.Companion_Default___.WrappedDefaultSimpleStringConfig())
  _86_valueOrError0 = _out7
  if (!(!((_86_valueOrError0).IsFailure()))) {
    panic("test/WrappedSimpleStringTest.dfy(11,19): " + (_86_valueOrError0).String())
  }
  _85_client = simpletypessmithystringinternaldafnytypes.Companion_ISimpleTypesStringClient_.CastTo_((_86_valueOrError0).Extract())
  SimpleStringImplTest.Companion_Default___.TestGetString(_85_client)
  SimpleStringImplTest.Companion_Default___.TestGetStringSingleValue(_85_client)
  SimpleStringImplTest.Companion_Default___.TestGetStringUTF8(_85_client)
}
// End of class Default__
