// Package SimpleBooleanImpl
// Dafny module SimpleBooleanImpl compiled into Go

package SimpleBooleanImpl

import (
	StandardLibrary "StandardLibrary"
	StandardLibrary_mUInt "StandardLibrary_mUInt"
	_System "System_"
	Wrappers "Wrappers"
	_dafny "dafny"
	os "os"
	simpletypesbooleaninternaldafnytypes "simpletypesbooleaninternaldafnytypes"
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

var Companion_Default___ = CompanionStruct_Default___{}

func (_this *Default__) Equals(other *Default__) bool {
	return _this == other
}

func (_this *Default__) EqualsGeneric(x interface{}) bool {
	other, ok := x.(*Default__)
	return ok && _this.Equals(other)
}

func (*Default__) String() string {
	return "SimpleBooleanImpl.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) GetBoolean(config Config, input simpletypesbooleaninternaldafnytypes.GetBooleanInput) Wrappers.Result {
	var output Wrappers.Result = Wrappers.Companion_Result_.Default(simpletypesbooleaninternaldafnytypes.Companion_GetBooleanOutput_.Default())
	_ = output
	if !(((input).Dtor_value()).Is_Some()) {
		panic("src/SimpleBooleanImpl.dfy(17,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	if !(((((input).Dtor_value()).Dtor_value().(bool)) == (true)) || ((((input).Dtor_value()).Dtor_value().(bool)) == (false))) {
		panic("src/SimpleBooleanImpl.dfy(19,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	var _72_res simpletypesbooleaninternaldafnytypes.GetBooleanOutput
	_ = _72_res
	_72_res = simpletypesbooleaninternaldafnytypes.Companion_GetBooleanOutput_.Create_GetBooleanOutput_((input).Dtor_value())
	if !(((((_72_res).Dtor_value()).Dtor_value().(bool)) == (true)) || ((((_72_res).Dtor_value()).Dtor_value().(bool)) == (false))) {
		panic("src/SimpleBooleanImpl.dfy(22,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	if !((((input).Dtor_value()).Dtor_value().(bool)) == (((_72_res).Dtor_value()).Dtor_value().(bool))) {
		panic("src/SimpleBooleanImpl.dfy(24,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	output = Wrappers.Companion_Result_.Create_Success_(_72_res)
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

var Companion_Config_ = CompanionStruct_Config_{}

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
		case 0:
			return Companion_Config_.Create_Config_(), true
		default:
			return Config{}, false
		}
	}
}

func (_this Config) String() string {
	switch _this.Get().(type) {
	case nil:
		return "null"
	case Config_Config:
		{
			return "SimpleBooleanImpl.Config.Config"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this Config) Equals(other Config) bool {
	switch _this.Get().(type) {
	case Config_Config:
		{
			_, ok := other.Get().(Config_Config)
			return ok
		}
	default:
		{
			return false // unexpected
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
	return Companion_Config_.Default()
}

func (_this type_Config_) String() string {
	return "SimpleBooleanImpl.Config"
}
func (_this Config) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = Config{}

// End of datatype Config
