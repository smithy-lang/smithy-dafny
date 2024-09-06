// Package SimpleAggregate
// Dafny module SimpleAggregate compiled into Go

package SimpleAggregate

import (
	os "os"

	_System "github.com/dafny-lang/DafnyRuntimeGo/System_"
	_dafny "github.com/dafny-lang/DafnyRuntimeGo/dafny"
	StandardLibrary "github.com/dafny-lang/DafnyStandardLibGo/StandardLibrary"
	StandardLibraryInterop "github.com/dafny-lang/DafnyStandardLibGo/StandardLibraryInterop"
	StandardLibrary_UInt "github.com/dafny-lang/DafnyStandardLibGo/StandardLibrary_UInt"
	Wrappers "github.com/dafny-lang/DafnyStandardLibGo/Wrappers"
	SimpleAggregateImpl "github.com/smithy-lang/smithy-dafny/TestModels/Aggregate/SimpleAggregateImpl"
	SimpleAggregateTypes "github.com/smithy-lang/smithy-dafny/TestModels/Aggregate/SimpleAggregateTypes"
)

var _ = os.Args
var _ _dafny.Dummy__
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_UInt.Dummy__
var _ StandardLibrary.Dummy__
var _ StandardLibraryInterop.Dummy__
var _ SimpleAggregateTypes.Dummy__
var _ SimpleAggregateImpl.Dummy__

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
	return "SimpleAggregate.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) DefaultSimpleAggregateConfig() SimpleAggregateTypes.SimpleAggregateConfig {
	return SimpleAggregateTypes.Companion_SimpleAggregateConfig_.Create_SimpleAggregateConfig_()
}
func (_static *CompanionStruct_Default___) SimpleAggregate(config SimpleAggregateTypes.SimpleAggregateConfig) Wrappers.Result {
	var res Wrappers.Result = Wrappers.Result{}
	_ = res
	var _3_client *SimpleAggregateClient
	_ = _3_client
	var _nw0 *SimpleAggregateClient = New_SimpleAggregateClient_()
	_ = _nw0
	_nw0.Ctor__(SimpleAggregateImpl.Companion_Config_.Create_Config_())
	_3_client = _nw0
	res = Wrappers.Companion_Result_.Create_Success_(_3_client)
	return res
	return res
}
func (_static *CompanionStruct_Default___) CreateSuccessOfClient(client SimpleAggregateTypes.ISimpleAggregateClient) Wrappers.Result {
	return Wrappers.Companion_Result_.Create_Success_(client)
}
func (_static *CompanionStruct_Default___) CreateFailureOfError(error_ SimpleAggregateTypes.Error) Wrappers.Result {
	return Wrappers.Companion_Result_.Create_Failure_(error_)
}

// End of class Default__

// Definition of class SimpleAggregateClient
type SimpleAggregateClient struct {
	_config SimpleAggregateImpl.Config
}

func New_SimpleAggregateClient_() *SimpleAggregateClient {
	_this := SimpleAggregateClient{}

	_this._config = SimpleAggregateImpl.Companion_Config_.Default()
	return &_this
}

type CompanionStruct_SimpleAggregateClient_ struct {
}

var Companion_SimpleAggregateClient_ = CompanionStruct_SimpleAggregateClient_{}

func (_this *SimpleAggregateClient) Equals(other *SimpleAggregateClient) bool {
	return _this == other
}

func (_this *SimpleAggregateClient) EqualsGeneric(x interface{}) bool {
	other, ok := x.(*SimpleAggregateClient)
	return ok && _this.Equals(other)
}

func (*SimpleAggregateClient) String() string {
	return "SimpleAggregate.SimpleAggregateClient"
}

func Type_SimpleAggregateClient_() _dafny.TypeDescriptor {
	return type_SimpleAggregateClient_{}
}

type type_SimpleAggregateClient_ struct {
}

func (_this type_SimpleAggregateClient_) Default() interface{} {
	return (*SimpleAggregateClient)(nil)
}

func (_this type_SimpleAggregateClient_) String() string {
	return "SimpleAggregate.SimpleAggregateClient"
}
func (_this *SimpleAggregateClient) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){SimpleAggregateTypes.Companion_ISimpleAggregateClient_.TraitID_}
}

var _ SimpleAggregateTypes.ISimpleAggregateClient = &SimpleAggregateClient{}
var _ _dafny.TraitOffspring = &SimpleAggregateClient{}

func (_this *SimpleAggregateClient) Ctor__(config SimpleAggregateImpl.Config) {
	{
		(_this)._config = config
	}
}
func (_this *SimpleAggregateClient) GetAggregate(input SimpleAggregateTypes.GetAggregateInput) Wrappers.Result {
	{
		var output Wrappers.Result = Wrappers.Companion_Result_.Default(SimpleAggregateTypes.Companion_GetAggregateOutput_.Default())
		_ = output
		var _out0 Wrappers.Result
		_ = _out0
		_out0 = SimpleAggregateImpl.Companion_Default___.GetAggregate((_this).Config(), input)
		output = _out0
		return output
	}
}
func (_this *SimpleAggregateClient) GetAggregateKnownValueTest(input SimpleAggregateTypes.GetAggregateInput) Wrappers.Result {
	{
		var output Wrappers.Result = Wrappers.Companion_Result_.Default(SimpleAggregateTypes.Companion_GetAggregateOutput_.Default())
		_ = output
		var _out1 Wrappers.Result
		_ = _out1
		_out1 = SimpleAggregateImpl.Companion_Default___.GetAggregateKnownValueTest((_this).Config(), input)
		output = _out1
		return output
	}
}
func (_this *SimpleAggregateClient) Config() SimpleAggregateImpl.Config {
	{
		return _this._config
	}
}

// End of class SimpleAggregateClient
