// Package SimpleStringImpl
// Dafny module SimpleStringImpl compiled into Go

package SimpleStringImpl

import (
  _dafny "dafny"
  os "os"
  _System "System_"
  Wrappers "Wrappers"
  StandardLibrary_mUInt "StandardLibrary_mUInt"
  StandardLibrary "StandardLibrary"
  UTF8 "UTF8"
  simpletypessmithystringinternaldafnytypes "simpletypessmithystringinternaldafnytypes"
)
var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_mUInt.Dummy__
var _ StandardLibrary.Dummy__

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
  return "SimpleStringImpl.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) GetString(config Config, input simpletypessmithystringinternaldafnytypes.GetStringInput) Wrappers.Result {
  var output Wrappers.Result = Wrappers.Companion_Result_.Default(simpletypessmithystringinternaldafnytypes.Companion_GetStringOutput_.Default())
  _ = output
  var _72_res simpletypessmithystringinternaldafnytypes.GetStringOutput
  _ = _72_res
  _72_res = simpletypessmithystringinternaldafnytypes.Companion_GetStringOutput_.Create_GetStringOutput_((input).Dtor_value())
  output = Wrappers.Companion_Result_.Create_Success_(_72_res)
  return output
  return output
}
func (_static *CompanionStruct_Default___) GetStringSingleValue(config Config, input simpletypessmithystringinternaldafnytypes.GetStringInput) Wrappers.Result {
  var output Wrappers.Result = Wrappers.Companion_Result_.Default(simpletypessmithystringinternaldafnytypes.Companion_GetStringOutput_.Default())
  _ = output
  if (!(((input).Dtor_value()).Is_Some())) {
    panic("src/SimpleStringImpl.dfy(28,8): " + (_dafny.SeqOfString("expectation violation")).String())
  }
  if (!(_dafny.Companion_Sequence_.Equal(((input).Dtor_value()).Dtor_value().(_dafny.Sequence), _dafny.SeqOfString("TEST_SIMPLE_STRING_SINGLE_VALUE")))) {
    panic("src/SimpleStringImpl.dfy(29,8): " + (_dafny.SeqOfString("expectation violation")).String())
  }
  var _73_res simpletypessmithystringinternaldafnytypes.GetStringOutput
  _ = _73_res
  _73_res = simpletypessmithystringinternaldafnytypes.Companion_GetStringOutput_.Create_GetStringOutput_((input).Dtor_value())
  output = Wrappers.Companion_Result_.Create_Success_(_73_res)
  return output
  return output
}
func (_static *CompanionStruct_Default___) GetStringUTF8(config Config, input simpletypessmithystringinternaldafnytypes.GetStringInput) Wrappers.Result {
  var output Wrappers.Result = Wrappers.Companion_Result_.Default(simpletypessmithystringinternaldafnytypes.Companion_GetStringOutput_.Default())
  _ = output
  if (!(((input).Dtor_value()).Is_Some())) {
    panic("src/SimpleStringImpl.dfy(35,8): " + (_dafny.SeqOfString("expectation violation")).String())
  }
  var _74_res simpletypessmithystringinternaldafnytypes.GetStringOutput
  _ = _74_res
  _74_res = simpletypessmithystringinternaldafnytypes.Companion_GetStringOutput_.Create_GetStringOutput_((input).Dtor_value())
  output = Wrappers.Companion_Result_.Create_Success_(_74_res)
  return output
  return output
}
// End of class Default__

// Definition of datatype Config
type Config struct {
  Data_Config_
}

func (_this Config) Get() Data_Config_ {
  return _this.Data_Config_
}

type Data_Config_ interface {
  isConfig()
}

type CompanionStruct_Config_ struct {
}
var Companion_Config_ = CompanionStruct_Config_ {
}

type Config_Config struct {
}

func (Config_Config) isConfig() {}

func (CompanionStruct_Config_) Create_Config_() Config {
  return Config{Config_Config{}}
}

func (_this Config) Is_Config() bool {
  _, ok := _this.Get().(Config_Config)
  return ok
}

func (CompanionStruct_Config_) Default() Config {
  return Companion_Config_.Create_Config_()
}

func (_ CompanionStruct_Config_) AllSingletonConstructors() _dafny.Iterator {
  i := -1
  return func() (interface{}, bool) {
    i++
    switch i {
      case 0: return Companion_Config_.Create_Config_(), true
      default: return Config{}, false
    }
  }
}

func (_this Config) String() string {
  switch _this.Get().(type) {
    case nil: return "null"
    case Config_Config: {
      return "SimpleStringImpl.Config.Config"
    }
    default: {
      return "<unexpected>"
    }
  }
}

func (_this Config) Equals(other Config) bool {
  switch _this.Get().(type) {
    case Config_Config: {
      _, ok := other.Get().(Config_Config)
      return ok
    }
    default: {
      return false; // unexpected
    }
  }
}

func (_this Config) EqualsGeneric(other interface{}) bool {
  typed, ok := other.(Config)
  return ok && _this.Equals(typed)
}

func Type_Config_() _dafny.TypeDescriptor {
  return type_Config_{}
}

type type_Config_ struct {
}

func (_this type_Config_) Default() interface{} {
  return Companion_Config_.Default();
}

func (_this type_Config_) String() string {
  return "SimpleStringImpl.Config"
}
func (_this Config) ParentTraits_() []*_dafny.TraitID {
  return [](*_dafny.TraitID){};
}
var _ _dafny.TraitOffspring = Config{}

// End of datatype Config
