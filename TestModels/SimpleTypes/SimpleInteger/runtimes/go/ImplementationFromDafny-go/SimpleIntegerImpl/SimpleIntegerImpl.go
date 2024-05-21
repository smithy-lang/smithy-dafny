// Package SimpleIntegerImpl
// Dafny module SimpleIntegerImpl compiled into Go

package SimpleIntegerImpl

import (
	os "os"

	StandardLibrary "github.com/ShubhamChaturvedi7/SimpleBoolean/StandardLibrary"
	StandardLibrary_UInt "github.com/ShubhamChaturvedi7/SimpleBoolean/StandardLibrary_UInt"
	Wrappers "github.com/ShubhamChaturvedi7/SimpleBoolean/Wrappers"
	simpletypesintegerinternaldafnytypes "github.com/ShubhamChaturvedi7/SimpleBoolean/simpletypesintegerinternaldafnytypes"
	_System "github.com/dafny-lang/DafnyRuntimeGo/System_"
	_dafny "github.com/dafny-lang/DafnyRuntimeGo/dafny"
)

var _ = os.Args
var _ _dafny.Dummy__
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_UInt.Dummy__
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
	return "SimpleIntegerImpl.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) GetInteger(config Config, input simpletypesintegerinternaldafnytypes.GetIntegerInput) Wrappers.Result {
	var output Wrappers.Result = Wrappers.Companion_Result_.Default(simpletypesintegerinternaldafnytypes.Companion_GetIntegerOutput_.Default())
	_ = output
	if !(((input).Dtor_value()).Is_Some()) {
		panic("src/SimpleIntegerImpl.dfy(20,8): " + (_dafny.UnicodeSeqOfUtf8Bytes("expectation violation")).VerbatimString(false))
	}
	if !(((((_dafny.Zero).Minus(StandardLibrary_UInt.Companion_Default___.INT32__MAX__LIMIT())).Int32()) <= (((input).Dtor_value()).UnwrapOr(int32(0)).(int32))) && ((((input).Dtor_value()).UnwrapOr(int32(0)).(int32)) <= (((StandardLibrary_UInt.Companion_Default___.INT32__MAX__LIMIT()).Minus(_dafny.One)).Int32()))) {
		panic("src/SimpleIntegerImpl.dfy(21,8): " + (_dafny.UnicodeSeqOfUtf8Bytes("expectation violation")).VerbatimString(false))
	}
	var _78_res simpletypesintegerinternaldafnytypes.GetIntegerOutput
	_ = _78_res
	_78_res = simpletypesintegerinternaldafnytypes.Companion_GetIntegerOutput_.Create_GetIntegerOutput_((input).Dtor_value())
	output = Wrappers.Companion_Result_.Create_Success_(_78_res)
	return output
	return output
}
func (_static *CompanionStruct_Default___) GetIntegerKnownValueTest(config Config, input simpletypesintegerinternaldafnytypes.GetIntegerInput) Wrappers.Result {
	var output Wrappers.Result = Wrappers.Companion_Result_.Default(simpletypesintegerinternaldafnytypes.Companion_GetIntegerOutput_.Default())
	_ = output
	if !(((input).Dtor_value()).Is_Some()) {
		panic("src/SimpleIntegerImpl.dfy(27,8): " + (_dafny.UnicodeSeqOfUtf8Bytes("expectation violation")).VerbatimString(false))
	}
	if !((((input).Dtor_value()).UnwrapOr(int32(0)).(int32)) == (int32(20))) {
		panic("src/SimpleIntegerImpl.dfy(28,8): " + (_dafny.UnicodeSeqOfUtf8Bytes("expectation violation")).VerbatimString(false))
	}
	var _79_res simpletypesintegerinternaldafnytypes.GetIntegerOutput
	_ = _79_res
	_79_res = simpletypesintegerinternaldafnytypes.Companion_GetIntegerOutput_.Create_GetIntegerOutput_((input).Dtor_value())
	output = Wrappers.Companion_Result_.Create_Success_(_79_res)
	return output
	return output
}

// End of class Default__

// Definition of datatype Config
type Config struct {
	Data_Config_
}

func (_this Config) Get_() Data_Config_ {
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
	_, ok := _this.Get_().(Config_Config)
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
	switch _this.Get_().(type) {
	case nil:
		return "null"
	case Config_Config:
		{
			return "SimpleIntegerImpl.Config.Config"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this Config) Equals(other Config) bool {
	switch _this.Get_().(type) {
	case Config_Config:
		{
			_, ok := other.Get_().(Config_Config)
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
	return "SimpleIntegerImpl.Config"
}
func (_this Config) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = Config{}

// End of datatype Config
