// Package simplepositionalinternaldafny
// Dafny module simplepositionalinternaldafny compiled into Go

package simplepositionalinternaldafny

import (
	"fmt"
	os "os"

	SimplePositionalImpl "github.com/Smithy-dafny/TestModels/Positional/SimplePositionalImpl"
	SimpleResource "github.com/Smithy-dafny/TestModels/Positional/SimpleResource"
	simplepositionalinternaldafnytypes "github.com/Smithy-dafny/TestModels/Positional/simplepositionalinternaldafnytypes"
	_System "github.com/dafny-lang/DafnyRuntimeGo/System_"
	_dafny "github.com/dafny-lang/DafnyRuntimeGo/dafny"
	StandardLibrary "github.com/dafny-lang/DafnyStandardLibGo/StandardLibrary"
	StandardLibraryInterop "github.com/dafny-lang/DafnyStandardLibGo/StandardLibraryInterop"
	StandardLibrary_UInt "github.com/dafny-lang/DafnyStandardLibGo/StandardLibrary_UInt"
	Wrappers "github.com/dafny-lang/DafnyStandardLibGo/Wrappers"
)

var _ = os.Args
var _ _dafny.Dummy__
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_UInt.Dummy__
var _ StandardLibrary.Dummy__
var _ StandardLibraryInterop.Dummy__
var _ SimpleResource.Dummy__
var _ SimplePositionalImpl.Dummy__

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
	return "simplepositionalinternaldafny.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) DefaultSimplePositionalConfig() simplepositionalinternaldafnytypes.SimplePositionalConfig {
	return simplepositionalinternaldafnytypes.Companion_SimplePositionalConfig_.Create_SimplePositionalConfig_()
}
func (_static *CompanionStruct_Default___) SimplePositional(config simplepositionalinternaldafnytypes.SimplePositionalConfig) Wrappers.Result {
	var res Wrappers.Result = Wrappers.Result{}
	_ = res
	var _4_client *SimplePositionalClient
	_ = _4_client
	var _nw2 *SimplePositionalClient = New_SimplePositionalClient_()
	_ = _nw2
	_nw2.Ctor__(SimplePositionalImpl.Companion_Config_.Create_Config_())
	_4_client = _nw2
	res = Wrappers.Companion_Result_.Create_Success_(_4_client)
	return res
	return res
}
func (_static *CompanionStruct_Default___) CreateSuccessOfClient(client simplepositionalinternaldafnytypes.ISimplePositionalClient) Wrappers.Result {
	return Wrappers.Companion_Result_.Create_Success_(client)
}
func (_static *CompanionStruct_Default___) CreateFailureOfError(error_ simplepositionalinternaldafnytypes.Error) Wrappers.Result {
	return Wrappers.Companion_Result_.Create_Failure_(error_)
}

// End of class Default__

// Definition of class SimplePositionalClient
type SimplePositionalClient struct {
	_config SimplePositionalImpl.Config
}

func New_SimplePositionalClient_() *SimplePositionalClient {
	_this := SimplePositionalClient{}

	_this._config = SimplePositionalImpl.Companion_Config_.Default()
	return &_this
}

type CompanionStruct_SimplePositionalClient_ struct {
}

var Companion_SimplePositionalClient_ = CompanionStruct_SimplePositionalClient_{}

func (_this *SimplePositionalClient) Equals(other *SimplePositionalClient) bool {
	return _this == other
}

func (_this *SimplePositionalClient) EqualsGeneric(x interface{}) bool {
	other, ok := x.(*SimplePositionalClient)
	return ok && _this.Equals(other)
}

func (*SimplePositionalClient) String() string {
	return "simplepositionalinternaldafny.SimplePositionalClient"
}

func Type_SimplePositionalClient_() _dafny.TypeDescriptor {
	return type_SimplePositionalClient_{}
}

type type_SimplePositionalClient_ struct {
}

func (_this type_SimplePositionalClient_) Default() interface{} {
	return (*SimplePositionalClient)(nil)
}

func (_this type_SimplePositionalClient_) String() string {
	return "simplepositionalinternaldafny.SimplePositionalClient"
}
func (_this *SimplePositionalClient) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){simplepositionalinternaldafnytypes.Companion_ISimplePositionalClient_.TraitID_}
}

var _ simplepositionalinternaldafnytypes.ISimplePositionalClient = &SimplePositionalClient{}
var _ _dafny.TraitOffspring = &SimplePositionalClient{}

func (_this *SimplePositionalClient) Ctor__(config SimplePositionalImpl.Config) {
	{
		(_this)._config = config
	}
}
func (_this *SimplePositionalClient) GetResource(input simplepositionalinternaldafnytypes.GetResourceInput) Wrappers.Result {
	{
		var output Wrappers.Result = Wrappers.Result{}
		_ = output
		var _out2 Wrappers.Result
		_ = _out2
		_out2 = SimplePositionalImpl.Companion_Default___.GetResource((_this).Config(), input)
		output = _out2
		return output
	}
}

// recover function to handle panic
func handlePanic() {

	// detect if panic occurs or not
	a := recover()

	if a != nil {
		fmt.Println("RECOVER in simplepositionalinternaldafny", a)
	}

}

func (_this *SimplePositionalClient) GetResourcePositional(input _dafny.Sequence) Wrappers.Result {
	{
		defer handlePanic()
		var output Wrappers.Result = Wrappers.Result{}
		_ = output
		var _out3 Wrappers.Result
		_ = _out3
		_out3 = SimplePositionalImpl.Companion_Default___.GetResourcePositional((_this).Config(), input)
		output = _out3
		return output
	}
}
func (_this *SimplePositionalClient) Config() SimplePositionalImpl.Config {
	{
		return _this._config
	}
}

// End of class SimplePositionalClient
