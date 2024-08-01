// Package SimplePositionalImplTest
// Dafny module SimplePositionalImplTest compiled into Go

package SimplePositionalImplTest

import (
	"fmt"
	os "os"

	SimplePositionalImpl "github.com/Smithy-dafny/TestModels/Positional/SimplePositionalImpl"
	SimpleResource "github.com/Smithy-dafny/TestModels/Positional/SimpleResource"
	simplepositionalinternaldafny "github.com/Smithy-dafny/TestModels/Positional/simplepositionalinternaldafny"
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
	return "SimplePositionalImplTest.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) TestClient(client simplepositionalinternaldafnytypes.ISimplePositionalClient) {
	Companion_Default___.TestGetResource(client)
	Companion_Default___.TestGetResourcePositional(client)
}
func (_static *CompanionStruct_Default___) TestGetResource(client simplepositionalinternaldafnytypes.ISimplePositionalClient) {
	var _5_input simplepositionalinternaldafnytypes.GetResourceInput
	_ = _5_input
	_5_input = simplepositionalinternaldafnytypes.Companion_GetResourceInput_.Create_GetResourceInput_(_dafny.SeqOfString("Test"))
	var _6_output simplepositionalinternaldafnytypes.GetResourceOutput
	_ = _6_output
	var _7_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _7_valueOrError0
	var _out4 Wrappers.Result
	_ = _out4
	_out4 = (client).GetResource(_5_input)
	_7_valueOrError0 = _out4
	if !(!((_7_valueOrError0).IsFailure())) {
		panic("test/SimplePositionalImplTest.dfy(27,22): " + (_7_valueOrError0).String())
	}
	_6_output = (_7_valueOrError0).Extract().(simplepositionalinternaldafnytypes.GetResourceOutput)
	var _8_resource simplepositionalinternaldafnytypes.ISimpleResource
	_ = _8_resource
	_8_resource = (_6_output).Dtor_output()
	var _9_getNameOutput simplepositionalinternaldafnytypes.GetNameOutput
	_ = _9_getNameOutput
	var _10_valueOrError1 Wrappers.Result = Wrappers.Companion_Result_.Default(simplepositionalinternaldafnytypes.Companion_GetNameOutput_.Default())
	_ = _10_valueOrError1
	var _out5 Wrappers.Result
	_ = _out5
	_out5 = (_8_resource).GetName(simplepositionalinternaldafnytypes.Companion_GetNameInput_.Create_GetNameInput_())
	_10_valueOrError1 = _out5
	if !(!((_10_valueOrError1).IsFailure())) {
		panic("test/SimplePositionalImplTest.dfy(29,29): " + (_10_valueOrError1).String())
	}
	_9_getNameOutput = (_10_valueOrError1).Extract().(simplepositionalinternaldafnytypes.GetNameOutput)
	if !(_dafny.Companion_Sequence_.Equal((_9_getNameOutput).Dtor_name(), _dafny.SeqOfString("Test"))) {
		panic("test/SimplePositionalImplTest.dfy(30,8): " + (_dafny.SeqOfString("expectation violation")).String())
	}
}

// recover function to handle panic
func handlePanic() {

	// detect if panic occurs or not
	a := recover()

	if a != nil {
		fmt.Println("RECOVER impl test", a)
	}

}
func (_static *CompanionStruct_Default___) TestGetResourcePositional(client simplepositionalinternaldafnytypes.ISimplePositionalClient) {
	defer handlePanic()
	var _11_input _dafny.Sequence
	_ = _11_input
	_11_input = _dafny.SeqOfString("TestPositional")
	var _12_resource simplepositionalinternaldafnytypes.ISimpleResource
	_ = _12_resource
	var _13_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _13_valueOrError0
	var _out6 Wrappers.Result
	_ = _out6
	_out6 = (client).GetResourcePositional(_11_input)
	_13_valueOrError0 = _out6
	if !(!((_13_valueOrError0).IsFailure())) {
		panic("test/SimplePositionalImplTest.dfy(39,47): " + (_13_valueOrError0).String())
	}
	_12_resource = simplepositionalinternaldafnytypes.Companion_ISimpleResource_.CastTo_((_13_valueOrError0).Extract())
	var _14_getNameOutput simplepositionalinternaldafnytypes.GetNameOutput
	_ = _14_getNameOutput
	var _15_valueOrError1 Wrappers.Result = Wrappers.Companion_Result_.Default(simplepositionalinternaldafnytypes.Companion_GetNameOutput_.Default())
	_ = _15_valueOrError1
	var _out7 Wrappers.Result
	_ = _out7

	_out7 = (_12_resource).GetName(simplepositionalinternaldafnytypes.Companion_GetNameInput_.Create_GetNameInput_())
	_15_valueOrError1 = _out7
	if !(!((_15_valueOrError1).IsFailure())) {
		panic("test/SimplePositionalImplTest.dfy(40,29): " + (_15_valueOrError1).String())
	}
	_14_getNameOutput = (_15_valueOrError1).Extract().(simplepositionalinternaldafnytypes.GetNameOutput)

	if !(_dafny.Companion_Sequence_.Equal((_14_getNameOutput).Dtor_name(), _dafny.SeqOfString("TestPositional"))) {
		panic("test/SimplePositionalImplTest.dfy(41,8): " + (_dafny.SeqOfString("expectation violation")).String())
	}
}
func (_static *CompanionStruct_Default___) TestDefaultConfig() {
	var _16_client *simplepositionalinternaldafny.SimplePositionalClient
	_ = _16_client
	var _17_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _17_valueOrError0
	var _out8 Wrappers.Result
	_ = _out8
	_out8 = simplepositionalinternaldafny.Companion_Default___.SimplePositional(simplepositionalinternaldafny.Companion_Default___.DefaultSimplePositionalConfig())
	_17_valueOrError0 = _out8
	if !(!((_17_valueOrError0).IsFailure())) {
		panic("test/SimplePositionalImplTest.dfy(45,22): " + (_17_valueOrError0).String())
	}
	_16_client = (_17_valueOrError0).Extract().(*simplepositionalinternaldafny.SimplePositionalClient)
	Companion_Default___.TestClient(_16_client)
}

// End of class Default__
