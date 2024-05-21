// Package SimpleBooleanImplTest
// Dafny module SimpleBooleanImplTest compiled into Go

package SimpleBooleanImplTest

import (
	SimpleBooleanImpl "SimpleBooleanImpl"
	StandardLibrary "StandardLibrary"
	StandardLibrary_mUInt "StandardLibrary_mUInt"
	_System "System_"
	Wrappers "Wrappers"
	_dafny "dafny"
	os "os"
	simpletypesbooleaninternaldafny "simpletypesbooleaninternaldafny"
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
	return "SimpleBooleanImplTest.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) GetBooleanTrue() {
	var _74_client *simpletypesbooleaninternaldafny.SimpleBooleanClient
	_ = _74_client
	var _75_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _75_valueOrError0
	var _out1 Wrappers.Result
	_ = _out1
	_out1 = simpletypesbooleaninternaldafny.Companion_Default___.SimpleBoolean(simpletypesbooleaninternaldafny.Companion_Default___.DefaultSimpleBooleanConfig())
	_75_valueOrError0 = _out1
	if !(!((_75_valueOrError0).IsFailure())) {
		panic("test/SimpleBooleanImplTest.dfy(10,19): " + (_75_valueOrError0).String())
	}
	_74_client = (_75_valueOrError0).Extract().(*simpletypesbooleaninternaldafny.SimpleBooleanClient)
	Companion_Default___.TestGetBooleanTrue(_74_client)
}
func (_static *CompanionStruct_Default___) GetBooleanFalse() {
	var _76_client *simpletypesbooleaninternaldafny.SimpleBooleanClient
	_ = _76_client
	var _77_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _77_valueOrError0
	var _out2 Wrappers.Result
	_ = _out2
	_out2 = simpletypesbooleaninternaldafny.Companion_Default___.SimpleBoolean(simpletypesbooleaninternaldafny.Companion_Default___.DefaultSimpleBooleanConfig())
	_77_valueOrError0 = _out2
	if !(!((_77_valueOrError0).IsFailure())) {
		panic("test/SimpleBooleanImplTest.dfy(14,19): " + (_77_valueOrError0).String())
	}
	_76_client = (_77_valueOrError0).Extract().(*simpletypesbooleaninternaldafny.SimpleBooleanClient)
	Companion_Default___.TestGetBooleanFalse(_76_client)
}
func (_static *CompanionStruct_Default___) TestGetBooleanTrue(client simpletypesbooleaninternaldafnytypes.ISimpleTypesBooleanClient) {
	var _78_ret simpletypesbooleaninternaldafnytypes.GetBooleanOutput
	_ = _78_ret
	var _79_valueOrError0 Wrappers.Result = Wrappers.Companion_Result_.Default(simpletypesbooleaninternaldafnytypes.Companion_GetBooleanOutput_.Default())
	_ = _79_valueOrError0
	var _out3 Wrappers.Result
	_ = _out3
	_out3 = (client).GetBoolean(simpletypesbooleaninternaldafnytypes.Companion_GetBooleanInput_.Create_GetBooleanInput_(Wrappers.Companion_Option_.Create_Some_(true)))
	_79_valueOrError0 = _out3
	if !(!((_79_valueOrError0).IsFailure())) {
		panic("test/SimpleBooleanImplTest.dfy(23,16): " + (_79_valueOrError0).String())
	}
	_78_ret = (_79_valueOrError0).Extract().(simpletypesbooleaninternaldafnytypes.GetBooleanOutput)
	if !((((_78_ret).Dtor_value()).UnwrapOr(false).(bool)) == (true)) {
		panic("test/SimpleBooleanImplTest.dfy(24,8): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	_dafny.Print(_78_ret)
}
func (_static *CompanionStruct_Default___) TestGetBooleanFalse(client simpletypesbooleaninternaldafnytypes.ISimpleTypesBooleanClient) {
	var _80_ret simpletypesbooleaninternaldafnytypes.GetBooleanOutput
	_ = _80_ret
	var _81_valueOrError0 Wrappers.Result = Wrappers.Companion_Result_.Default(simpletypesbooleaninternaldafnytypes.Companion_GetBooleanOutput_.Default())
	_ = _81_valueOrError0
	var _out4 Wrappers.Result
	_ = _out4
	_out4 = (client).GetBoolean(simpletypesbooleaninternaldafnytypes.Companion_GetBooleanInput_.Create_GetBooleanInput_(Wrappers.Companion_Option_.Create_Some_(false)))
	_81_valueOrError0 = _out4
	if !(!((_81_valueOrError0).IsFailure())) {
		panic("test/SimpleBooleanImplTest.dfy(33,16): " + (_81_valueOrError0).String())
	}
	_80_ret = (_81_valueOrError0).Extract().(simpletypesbooleaninternaldafnytypes.GetBooleanOutput)
	if !((((_80_ret).Dtor_value()).UnwrapOr(true).(bool)) == (false)) {
		panic("test/SimpleBooleanImplTest.dfy(34,8): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	_dafny.Print(_80_ret)
}

// End of class Default__
