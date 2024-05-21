// Package SimpleConstraintsImplTest
// Dafny module SimpleConstraintsImplTest compiled into Go

package SimpleConstraintsImplTest

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
)
var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_mUInt.Dummy__
var _ StandardLibrary.Dummy__
var _ SimpleConstraintsImpl.Dummy__
var _ Helpers.Dummy__

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
  return "SimpleConstraintsImplTest.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) TestConstraints() {
  var _108_client *simpleconstraintsinternaldafny.SimpleConstraintsClient
  _ = _108_client
  var _109_valueOrError0 Wrappers.Result = Wrappers.Result{}
  _ = _109_valueOrError0
  var _out5 Wrappers.Result
  _ = _out5
  _out5 = simpleconstraintsinternaldafny.Companion_Default___.SimpleConstraints(simpleconstraintsinternaldafny.Companion_Default___.DefaultSimpleConstraintsConfig())
  _109_valueOrError0 = _out5
  if (!(!((_109_valueOrError0).IsFailure()))) {
    panic("test/SimpleConstraintsImplTest.dfy(15,19): " + (_109_valueOrError0).String())
  }
  _108_client = (_109_valueOrError0).Extract().(*simpleconstraintsinternaldafny.SimpleConstraintsClient)
  Companion_Default___.TestGetConstraintWithValidInputs(_108_client)
}
func (_static *CompanionStruct_Default___) TestGetConstraintWithValidInputs(client simple.constraints.internaldafny.types.ISimpleConstraintsClient) {
  var _110_input simple.constraints.internaldafny.types.GetConstraintsInput
  _ = _110_input
  var _out6 simple.constraints.internaldafny.types.GetConstraintsInput
  _ = _out6
  _out6 = Helpers.Companion_Default___.GetConstraintsInputTemplate(_dafny.SetOf())
  _110_input = _out6
  var _111_ret Wrappers.Result
  _ = _111_ret
  var _out7 Wrappers.Result
  _ = _out7
  _out7 = (client).GetConstraints(_110_input)
  _111_ret = _out7
  if (!((_111_ret).Is_Success())) {
    panic("test/SimpleConstraintsImplTest.dfy(26,6): " + (_dafny.SeqOfString("expectation violation")).String())
  }
}
// End of class Default__
