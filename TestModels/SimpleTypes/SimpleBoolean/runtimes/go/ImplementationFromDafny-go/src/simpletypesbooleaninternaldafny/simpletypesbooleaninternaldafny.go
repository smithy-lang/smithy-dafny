// Package simpletypesbooleaninternaldafny
// Dafny module simpletypesbooleaninternaldafny compiled into Go

package simpletypesbooleaninternaldafny

import (
	SimpleBooleanImpl "SimpleBooleanImpl"
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
var _ SimpleBooleanImpl.Dummy__

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
	return "simpletypesbooleaninternaldafny.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) DefaultSimpleBooleanConfig() simpletypesbooleaninternaldafnytypes.SimpleBooleanConfig {
	return simpletypesbooleaninternaldafnytypes.Companion_SimpleBooleanConfig_.Create_SimpleBooleanConfig_()
}
func (_static *CompanionStruct_Default___) SimpleBoolean(config simpletypesbooleaninternaldafnytypes.SimpleBooleanConfig) Wrappers.Result {
	var res Wrappers.Result = Wrappers.Result{}
	_ = res
	var _73_client *SimpleBooleanClient
	_ = _73_client
	var _nw1 *SimpleBooleanClient = New_SimpleBooleanClient_()
	_ = _nw1
	_nw1.Ctor__(SimpleBooleanImpl.Companion_Config_.Create_Config_())
	_73_client = _nw1
	res = Wrappers.Companion_Result_.Create_Success_(_73_client)
	return res
	return res
}

// End of class Default__

// Definition of class SimpleBooleanClient
type SimpleBooleanClient struct {
	_config SimpleBooleanImpl.Config
}

func New_SimpleBooleanClient_() *SimpleBooleanClient {
	_this := SimpleBooleanClient{}

	_this._config = SimpleBooleanImpl.Companion_Config_.Default()
	return &_this
}

type CompanionStruct_SimpleBooleanClient_ struct {
}

var Companion_SimpleBooleanClient_ = CompanionStruct_SimpleBooleanClient_{}

func (_this *SimpleBooleanClient) Equals(other *SimpleBooleanClient) bool {
	return _this == other
}

func (_this *SimpleBooleanClient) EqualsGeneric(x interface{}) bool {
	other, ok := x.(*SimpleBooleanClient)
	return ok && _this.Equals(other)
}

func (*SimpleBooleanClient) String() string {
	return "simpletypesbooleaninternaldafny.SimpleBooleanClient"
}

func Type_SimpleBooleanClient_() _dafny.TypeDescriptor {
	return type_SimpleBooleanClient_{}
}

type type_SimpleBooleanClient_ struct {
}

func (_this type_SimpleBooleanClient_) Default() interface{} {
	return (*SimpleBooleanClient)(nil)
}

func (_this type_SimpleBooleanClient_) String() string {
	return "simpletypesbooleaninternaldafny.SimpleBooleanClient"
}
func (_this *SimpleBooleanClient) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){simpletypesbooleaninternaldafnytypes.Companion_ISimpleTypesBooleanClient_.TraitID_}
}

var _ simpletypesbooleaninternaldafnytypes.ISimpleTypesBooleanClient = &SimpleBooleanClient{}
var _ _dafny.TraitOffspring = &SimpleBooleanClient{}

func (_this *SimpleBooleanClient) Ctor__(config SimpleBooleanImpl.Config) {
	{
		(_this)._config = config
	}
}
func (_this *SimpleBooleanClient) GetBoolean(input simpletypesbooleaninternaldafnytypes.GetBooleanInput) Wrappers.Result {
	{
		var output Wrappers.Result = Wrappers.Companion_Result_.Default(simpletypesbooleaninternaldafnytypes.Companion_GetBooleanOutput_.Default())
		_ = output
		var _out0 Wrappers.Result
		_ = _out0
		_out0 = SimpleBooleanImpl.Companion_Default___.GetBoolean((_this).Config(), input)
		output = _out0
		return output
	}
}
func (_this *SimpleBooleanClient) Config() SimpleBooleanImpl.Config {
	{
		return _this._config
	}
}

// End of class SimpleBooleanClient
