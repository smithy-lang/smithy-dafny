// Package WrappedSimpleConstraintsTest
// Dafny module WrappedSimpleConstraintsTest compiled into Go

package WrappedSimpleConstraintsTest

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
  return "WrappedSimpleConstraintsTest.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) GetConstraints() {
  var _112_client simple.constraints.internaldafny.types.ISimpleConstraintsClient
  _ = _112_client
  var _113_valueOrError0 Wrappers.Result = Wrappers.Result{}
  _ = _113_valueOrError0
  var _out8 Wrappers.Result
  _ = _out8
  _out8 = simpleconstraintsinternaldafnywrapped.WrappedSimpleConstraints(simpleconstraintsinternaldafnywrapped.Companion_Default___.WrappedDefaultSimpleConstraintsConfig())
  _113_valueOrError0 = _out8
  if (!(!((_113_valueOrError0).IsFailure()))) {
    panic("test/WrappedSimpleConstraintsTest.dfy(11,19): " + (_113_valueOrError0).String())
  }
  _112_client = simple.constraints.internaldafny.types.Companion_ISimpleConstraintsClient_.CastTo_((_113_valueOrError0).Extract())
  SimpleConstraintsImplTest.Companion_Default___.TestGetConstraintWithValidInputs(_112_client)
}
// End of class Default__
