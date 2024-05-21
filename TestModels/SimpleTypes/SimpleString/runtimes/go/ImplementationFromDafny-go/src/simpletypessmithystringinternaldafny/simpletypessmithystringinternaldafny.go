// Package simpletypessmithystringinternaldafny
// Dafny module simpletypessmithystringinternaldafny compiled into Go

package simpletypessmithystringinternaldafny

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
  return "simpletypessmithystringinternaldafny.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) DefaultSimpleStringConfig() simpletypessmithystringinternaldafnytypes.SimpleStringConfig {
  return simpletypessmithystringinternaldafnytypes.Companion_SimpleStringConfig_.Create_SimpleStringConfig_()
}
func (_static *CompanionStruct_Default___) SimpleString(config simpletypessmithystringinternaldafnytypes.SimpleStringConfig) Wrappers.Result {
  var res Wrappers.Result = Wrappers.Result{}
  _ = res
  var _75_client *SimpleStringClient
  _ = _75_client
  var _nw1 *SimpleStringClient = New_SimpleStringClient_()
  _ = _nw1
  _nw1.Ctor__(SimpleStringImpl.Companion_Config_.Create_Config_())
  _75_client = _nw1
  res = Wrappers.Companion_Result_.Create_Success_(_75_client)
  return res
  return res
}
// End of class Default__

// Definition of class SimpleStringClient
type SimpleStringClient struct {
  _config SimpleStringImpl.Config
}

func New_SimpleStringClient_() *SimpleStringClient {
  _this := SimpleStringClient{}

  _this._config = SimpleStringImpl.Companion_Config_.Default()
  return &_this
}

type CompanionStruct_SimpleStringClient_ struct {
}
var Companion_SimpleStringClient_ = CompanionStruct_SimpleStringClient_ {
}

func (_this *SimpleStringClient) Equals(other *SimpleStringClient) bool {
  return _this == other
}

func (_this *SimpleStringClient) EqualsGeneric(x interface{}) bool {
  other, ok := x.(*SimpleStringClient)
  return ok && _this.Equals(other)
}

func (*SimpleStringClient) String() string {
  return "simpletypessmithystringinternaldafny.SimpleStringClient"
}

func Type_SimpleStringClient_() _dafny.TypeDescriptor {
  return type_SimpleStringClient_{}
}

type type_SimpleStringClient_ struct {
}

func (_this type_SimpleStringClient_) Default() interface{} {
  return (*SimpleStringClient)(nil)
}

func (_this type_SimpleStringClient_) String() string {
  return "simpletypessmithystringinternaldafny.SimpleStringClient"
}
func (_this *SimpleStringClient) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){simpletypessmithystringinternaldafnytypes.Companion_ISimpleTypesStringClient_.TraitID_};
}
var _ simpletypessmithystringinternaldafnytypes.ISimpleTypesStringClient = &SimpleStringClient{}
var _ _dafny.TraitOffspring = &SimpleStringClient{}

func (_this *SimpleStringClient) Ctor__(config SimpleStringImpl.Config) {
  {
    (_this)._config = config
  }
}
func (_this *SimpleStringClient) GetString(input simpletypessmithystringinternaldafnytypes.GetStringInput) Wrappers.Result {
  {
    var output Wrappers.Result = Wrappers.Companion_Result_.Default(simpletypessmithystringinternaldafnytypes.Companion_GetStringOutput_.Default())
    _ = output
    var _out0 Wrappers.Result
    _ = _out0
    _out0 = SimpleStringImpl.Companion_Default___.GetString((_this).Config(), input)
    output = _out0
    return output
  }
}
func (_this *SimpleStringClient) GetStringSingleValue(input simpletypessmithystringinternaldafnytypes.GetStringInput) Wrappers.Result {
  {
    var output Wrappers.Result = Wrappers.Companion_Result_.Default(simpletypessmithystringinternaldafnytypes.Companion_GetStringOutput_.Default())
    _ = output
    var _out1 Wrappers.Result
    _ = _out1
    _out1 = SimpleStringImpl.Companion_Default___.GetStringSingleValue((_this).Config(), input)
    output = _out1
    return output
  }
}
func (_this *SimpleStringClient) GetStringUTF8(input simpletypessmithystringinternaldafnytypes.GetStringInput) Wrappers.Result {
  {
    var output Wrappers.Result = Wrappers.Companion_Result_.Default(simpletypessmithystringinternaldafnytypes.Companion_GetStringOutput_.Default())
    _ = output
    var _out2 Wrappers.Result
    _ = _out2
    _out2 = SimpleStringImpl.Companion_Default___.GetStringUTF8((_this).Config(), input)
    output = _out2
    return output
  }
}
func (_this *SimpleStringClient) Config() SimpleStringImpl.Config {
  {
    return _this._config
  }
}
// End of class SimpleStringClient
