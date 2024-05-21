// Package simpletypesintegerinternaldafny
// Dafny module simpletypesintegerinternaldafny compiled into Go

package simpletypesintegerinternaldafny

import (
	os "os"

	SimpleIntegerImpl "github.com/ShubhamChaturvedi7/SimpleBoolean/SimpleIntegerImpl"
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
var _ SimpleIntegerImpl.Dummy__

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
	return "simpletypesintegerinternaldafny.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) DefaultSimpleIntegerConfig() simpletypesintegerinternaldafnytypes.SimpleIntegerConfig {
	return simpletypesintegerinternaldafnytypes.Companion_SimpleIntegerConfig_.Create_SimpleIntegerConfig_()
}
func (_static *CompanionStruct_Default___) SimpleInteger(config simpletypesintegerinternaldafnytypes.SimpleIntegerConfig) Wrappers.Result {
	var res Wrappers.Result = Wrappers.Result{}
	_ = res
	var _80_client *SimpleIntegerClient
	_ = _80_client
	var _nw1 *SimpleIntegerClient = New_SimpleIntegerClient_()
	_ = _nw1
	_nw1.Ctor__(SimpleIntegerImpl.Companion_Config_.Create_Config_())
	_80_client = _nw1
	res = Wrappers.Companion_Result_.Create_Success_(_80_client)
	return res
	return res
}
func (_static *CompanionStruct_Default___) CreateSuccessOfClient(client simpletypesintegerinternaldafnytypes.ISimpleTypesIntegerClient) Wrappers.Result {
	return Wrappers.Companion_Result_.Create_Success_(client)
}
func (_static *CompanionStruct_Default___) CreateFailureOfError(error_ simpletypesintegerinternaldafnytypes.Error) Wrappers.Result {
	return Wrappers.Companion_Result_.Create_Failure_(error_)
}

// End of class Default__

// Definition of class SimpleIntegerClient
type SimpleIntegerClient struct {
	_config SimpleIntegerImpl.Config
}

func New_SimpleIntegerClient_() *SimpleIntegerClient {
	_this := SimpleIntegerClient{}

	_this._config = SimpleIntegerImpl.Companion_Config_.Default()
	return &_this
}

type CompanionStruct_SimpleIntegerClient_ struct {
}

var Companion_SimpleIntegerClient_ = CompanionStruct_SimpleIntegerClient_{}

func (_this *SimpleIntegerClient) Equals(other *SimpleIntegerClient) bool {
	return _this == other
}

func (_this *SimpleIntegerClient) EqualsGeneric(x interface{}) bool {
	other, ok := x.(*SimpleIntegerClient)
	return ok && _this.Equals(other)
}

func (*SimpleIntegerClient) String() string {
	return "simpletypesintegerinternaldafny.SimpleIntegerClient"
}

func Type_SimpleIntegerClient_() _dafny.TypeDescriptor {
	return type_SimpleIntegerClient_{}
}

type type_SimpleIntegerClient_ struct {
}

func (_this type_SimpleIntegerClient_) Default() interface{} {
	return (*SimpleIntegerClient)(nil)
}

func (_this type_SimpleIntegerClient_) String() string {
	return "simpletypesintegerinternaldafny.SimpleIntegerClient"
}
func (_this *SimpleIntegerClient) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){simpletypesintegerinternaldafnytypes.Companion_ISimpleTypesIntegerClient_.TraitID_}
}

var _ simpletypesintegerinternaldafnytypes.ISimpleTypesIntegerClient = &SimpleIntegerClient{}
var _ _dafny.TraitOffspring = &SimpleIntegerClient{}

func (_this *SimpleIntegerClient) Ctor__(config SimpleIntegerImpl.Config) {
	{
		(_this)._config = config
	}
}
func (_this *SimpleIntegerClient) GetInteger(input simpletypesintegerinternaldafnytypes.GetIntegerInput) Wrappers.Result {
	{
		var output Wrappers.Result = Wrappers.Companion_Result_.Default(simpletypesintegerinternaldafnytypes.Companion_GetIntegerOutput_.Default())
		_ = output
		var _out0 Wrappers.Result
		_ = _out0
		_out0 = SimpleIntegerImpl.Companion_Default___.GetInteger((_this).Config(), input)
		output = _out0
		return output
	}
}
func (_this *SimpleIntegerClient) GetIntegerKnownValueTest(input simpletypesintegerinternaldafnytypes.GetIntegerInput) Wrappers.Result {
	{
		var output Wrappers.Result = Wrappers.Companion_Result_.Default(simpletypesintegerinternaldafnytypes.Companion_GetIntegerOutput_.Default())
		_ = output
		var _out1 Wrappers.Result
		_ = _out1
		_out1 = SimpleIntegerImpl.Companion_Default___.GetIntegerKnownValueTest((_this).Config(), input)
		output = _out1
		return output
	}
}
func (_this *SimpleIntegerClient) Config() SimpleIntegerImpl.Config {
	{
		return _this._config
	}
}

// End of class SimpleIntegerClient
