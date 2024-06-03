// Package SimpleExternImpl
// Dafny module SimpleExternImpl compiled into Go

package SimpleExternImpl

import (
	ExternConstructor "ExternConstructor"
	StandardLibrary "StandardLibrary"
	StandardLibraryInterop "StandardLibraryInterop"
	StandardLibrary_UInt "StandardLibrary_UInt"
	_System "System_"
	Wrappers "Wrappers"
	_dafny "dafny"
	os "os"
	simpledafnyexterninternaldafnytypes "simpledafnyexterninternaldafnytypes"
	"types"
)

var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_UInt.Dummy__
var _ StandardLibrary.Dummy__
var _ StandardLibraryInterop.Dummy__

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
	return "SimpleExternImpl.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) UseClassExtern(config Config, input simpledafnyexterninternaldafnytypes.UseClassExternInput) Wrappers.Result {
	var output Wrappers.Result = Wrappers.Companion_Result_.Default(simpledafnyexterninternaldafnytypes.Companion_UseClassExternOutput_.Default())
	_ = output
	var _1_externClassObject *ExternConstructor.ExternConstructorClass
	_ = _1_externClassObject
	var _2_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _2_valueOrError0
	var _out0 Wrappers.Result
	_ = _out0
	_out0 = ExternConstructor.Companion_ExternConstructorClass_.Build(((input).Dtor_value()).UnwrapOr(_dafny.SeqOfString("Error")).(_dafny.Sequence))
	_2_valueOrError0 = _out0
	if (_2_valueOrError0).IsFailure() {
		output = (_2_valueOrError0).PropagateFailure()
		return output
	}
	_1_externClassObject = (_2_valueOrError0).Extract().(*ExternConstructor.ExternConstructorClass)
	var _3_res _dafny.Sequence
	_ = _3_res
	var _4_valueOrError1 Wrappers.Result = Wrappers.Companion_Result_.Default(_dafny.EmptySeq.SetString())
	_ = _4_valueOrError1
	var _out1 Wrappers.Result
	_ = _out1
	_out1 = (_1_externClassObject).GetValue()
	_4_valueOrError1 = _out1
	if (_4_valueOrError1).IsFailure() {
		output = (_4_valueOrError1).PropagateFailure()
		return output
	}
	_3_res = (_4_valueOrError1).Extract().(_dafny.Sequence)
	output = Wrappers.Companion_Result_.Create_Success_(simpledafnyexterninternaldafnytypes.Companion_UseClassExternOutput_.Create_UseClassExternOutput_(Wrappers.Companion_Option_.Create_Some_(_3_res)))
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
			return "SimpleExternImpl.Config.Config"
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
	return "SimpleExternImpl.Config"
}
func (_this Config) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = Config{}

// End of datatype Config

func (CompanionStruct_Default___) GetExtern(c Config, input simpledafnyexterninternaldafnytypes.GetExternInput) Wrappers.Result {
	return Wrappers.Companion_Result_.Create_Success_(simpledafnyexterninternaldafnytypes.Companion_GetExternOutput_.Create_GetExternOutput_(input.Dtor_blobValue(),
		input.Dtor_booleanValue(),
		input.Dtor_stringValue(),
		input.Dtor_integerValue(),
		input.Dtor_longValue()))

}
func (CompanionStruct_Default___) ExternMustError(c Config, input simpledafnyexterninternaldafnytypes.ExternMustErrorInput) Wrappers.Result {

	return Wrappers.Companion_Result_.Create_Failure_(
		simpledafnyexterninternaldafnytypes.Companion_Error_.Create_Opaque_(types.OpaqueError{
			input.Dtor_value()}))

}
