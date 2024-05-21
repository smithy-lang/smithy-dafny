// Package simpleconstraintsinternaldafny
// Dafny module simpleconstraintsinternaldafny compiled into Go

package simpleconstraintsinternaldafny

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
)
var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_mUInt.Dummy__
var _ StandardLibrary.Dummy__
var _ SimpleConstraintsImpl.Dummy__

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
  return "simpleconstraintsinternaldafny.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) DefaultSimpleConstraintsConfig() simple.constraints.internaldafny.types.SimpleConstraintsConfig {
  return simple.constraints.internaldafny.types.Companion_SimpleConstraintsConfig_.Create_SimpleConstraintsConfig_()
}
func (_static *CompanionStruct_Default___) SimpleConstraints(config simple.constraints.internaldafny.types.SimpleConstraintsConfig) Wrappers.Result {
  var res Wrappers.Result = Wrappers.Result{}
  _ = res
  var _73_client *SimpleConstraintsClient
  _ = _73_client
  var _nw1 *SimpleConstraintsClient = New_SimpleConstraintsClient_()
  _ = _nw1
  _nw1.Ctor__(SimpleConstraintsImpl.Companion_Config_.Create_Config_())
  _73_client = _nw1
  res = Wrappers.Companion_Result_.Create_Success_(_73_client)
  return res
  return res
}
// End of class Default__

// Definition of class SimpleConstraintsClient
type SimpleConstraintsClient struct {
  _config SimpleConstraintsImpl.Config
}

func New_SimpleConstraintsClient_() *SimpleConstraintsClient {
  _this := SimpleConstraintsClient{}

  _this._config = SimpleConstraintsImpl.Companion_Config_.Default()
  return &_this
}

type CompanionStruct_SimpleConstraintsClient_ struct {
}
var Companion_SimpleConstraintsClient_ = CompanionStruct_SimpleConstraintsClient_ {
}

func (_this *SimpleConstraintsClient) Equals(other *SimpleConstraintsClient) bool {
  return _this == other
}

func (_this *SimpleConstraintsClient) EqualsGeneric(x interface{}) bool {
  other, ok := x.(*SimpleConstraintsClient)
  return ok && _this.Equals(other)
}

func (*SimpleConstraintsClient) String() string {
  return "simpleconstraintsinternaldafny.SimpleConstraintsClient"
}

func Type_SimpleConstraintsClient_() _dafny.TypeDescriptor {
  return type_SimpleConstraintsClient_{}
}

type type_SimpleConstraintsClient_ struct {
}

func (_this type_SimpleConstraintsClient_) Default() interface{} {
  return (*SimpleConstraintsClient)(nil)
}

func (_this type_SimpleConstraintsClient_) String() string {
  return "simpleconstraintsinternaldafny.SimpleConstraintsClient"
}
func (_this *SimpleConstraintsClient) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){simple.constraints.internaldafny.types.Companion_ISimpleConstraintsClient_.TraitID_};
}
var _ simple.constraints.internaldafny.types.ISimpleConstraintsClient = &SimpleConstraintsClient{}
var _ _dafny.TraitOffspring = &SimpleConstraintsClient{}

func (_this *SimpleConstraintsClient) Ctor__(config SimpleConstraintsImpl.Config) {
  {
    (_this)._config = config
  }
}
func (_this *SimpleConstraintsClient) GetConstraints(input simple.constraints.internaldafny.types.GetConstraintsInput) Wrappers.Result {
  {
    var output Wrappers.Result = Wrappers.Companion_Result_.Default(simple.constraints.internaldafny.types.Companion_GetConstraintsOutput_.Default())
    _ = output
    var _out0 Wrappers.Result
    _ = _out0
    _out0 = SimpleConstraintsImpl.Companion_Default___.GetConstraints((_this).Config(), input)
    output = _out0
    return output
  }
}
func (_this *SimpleConstraintsClient) Config() SimpleConstraintsImpl.Config {
  {
    return _this._config
  }
}
// End of class SimpleConstraintsClient
