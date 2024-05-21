// Package SimpleIntegerImplTest
// Dafny module SimpleIntegerImplTest compiled into Go

package SimpleIntegerImplTest

import (
	os "os"

	SimpleIntegerImpl "github.com/ShubhamChaturvedi7/SimpleBoolean/SimpleIntegerImpl"
	StandardLibrary "github.com/ShubhamChaturvedi7/SimpleBoolean/StandardLibrary"
	StandardLibraryInterop "github.com/ShubhamChaturvedi7/SimpleBoolean/StandardLibraryInterop"
	StandardLibrary_UInt "github.com/ShubhamChaturvedi7/SimpleBoolean/StandardLibrary_UInt"
	Wrappers "github.com/ShubhamChaturvedi7/SimpleBoolean/Wrappers"
	simpletypesintegerinternaldafny "github.com/ShubhamChaturvedi7/SimpleBoolean/simpletypesintegerinternaldafny"
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
	return "SimpleIntegerImplTest.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) GetInteger() {
	var _81_client *simpletypesintegerinternaldafny.SimpleIntegerClient
	_ = _81_client
	var _82_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _82_valueOrError0
	var _out2 Wrappers.Result
	_ = _out2
	_out2 = simpletypesintegerinternaldafny.Companion_Default___.SimpleInteger(simpletypesintegerinternaldafny.Companion_Default___.DefaultSimpleIntegerConfig())
	_82_valueOrError0 = _out2
	if !(!((_82_valueOrError0).IsFailure())) {
		panic("test/SimpleIntegerImplTest.dfy(11,22): " + (_82_valueOrError0).String())
	}
	_81_client = (_82_valueOrError0).Extract().(*simpletypesintegerinternaldafny.SimpleIntegerClient)
	Companion_Default___.TestGetInteger(_81_client)
	Companion_Default___.TestGetIntegerKnownValue(_81_client)
	Companion_Default___.TestGetIntegerEdgeCases(_81_client)
}
func (_static *CompanionStruct_Default___) TestGetInteger(client simpletypesintegerinternaldafnytypes.ISimpleTypesIntegerClient) {
	var _83_ret simpletypesintegerinternaldafnytypes.GetIntegerOutput
	_ = _83_ret
	var _84_valueOrError0 Wrappers.Result = Wrappers.Companion_Result_.Default(simpletypesintegerinternaldafnytypes.Companion_GetIntegerOutput_.Default())
	_ = _84_valueOrError0
	var _out3 Wrappers.Result
	_ = _out3
	_out3 = (client).GetInteger(simpletypesintegerinternaldafnytypes.Companion_GetIntegerInput_.Create_GetIntegerInput_(Wrappers.Companion_Option_.Create_Some_(int32(1))))
	_84_valueOrError0 = _out3
	if !(!((_84_valueOrError0).IsFailure())) {
		panic("test/SimpleIntegerImplTest.dfy(22,19): " + (_84_valueOrError0).String())
	}
	_83_ret = (_84_valueOrError0).Extract().(simpletypesintegerinternaldafnytypes.GetIntegerOutput)
	if !((((_83_ret).Dtor_value()).UnwrapOr(int32(0)).(int32)) == (int32(1))) {
		panic("test/SimpleIntegerImplTest.dfy(23,8): " + (_dafny.UnicodeSeqOfUtf8Bytes("expectation violation")).VerbatimString(false))
	}
	_dafny.Print(_83_ret)
}
func (_static *CompanionStruct_Default___) TestGetIntegerKnownValue(client simpletypesintegerinternaldafnytypes.ISimpleTypesIntegerClient) {
	var _85_ret simpletypesintegerinternaldafnytypes.GetIntegerOutput
	_ = _85_ret
	var _86_valueOrError0 Wrappers.Result = Wrappers.Companion_Result_.Default(simpletypesintegerinternaldafnytypes.Companion_GetIntegerOutput_.Default())
	_ = _86_valueOrError0
	var _out4 Wrappers.Result
	_ = _out4
	_out4 = (client).GetIntegerKnownValueTest(simpletypesintegerinternaldafnytypes.Companion_GetIntegerInput_.Create_GetIntegerInput_(Wrappers.Companion_Option_.Create_Some_(int32(20))))
	_86_valueOrError0 = _out4
	if !(!((_86_valueOrError0).IsFailure())) {
		panic("test/SimpleIntegerImplTest.dfy(32,19): " + (_86_valueOrError0).String())
	}
	_85_ret = (_86_valueOrError0).Extract().(simpletypesintegerinternaldafnytypes.GetIntegerOutput)
	if !((((_85_ret).Dtor_value()).UnwrapOr(int32(0)).(int32)) == (int32(20))) {
		panic("test/SimpleIntegerImplTest.dfy(33,8): " + (_dafny.UnicodeSeqOfUtf8Bytes("expectation violation")).VerbatimString(false))
	}
	_dafny.Print(_85_ret)
}
func (_static *CompanionStruct_Default___) TestGetIntegerEdgeCases(client simpletypesintegerinternaldafnytypes.ISimpleTypesIntegerClient) {
	var _87_inputInteger _dafny.Sequence
	_ = _87_inputInteger
	_87_inputInteger = _dafny.SeqOf(int32(-1), int32(0), int32(1), ((StandardLibrary_UInt.Companion_Default___.INT32__MAX__LIMIT()).Minus(_dafny.One)).Int32(), (int32(0))-(((StandardLibrary_UInt.Companion_Default___.INT32__MAX__LIMIT()).Minus(_dafny.One)).Int32()))
	var _hi1 _dafny.Int = _dafny.IntOfUint32((_87_inputInteger).Cardinality())
	_ = _hi1
	for _88_i := _dafny.Zero; _88_i.Cmp(_hi1) < 0; _88_i = _88_i.Plus(_dafny.One) {
		var _89_integerValue int32
		_ = _89_integerValue
		_89_integerValue = (_87_inputInteger).Select((_88_i).Uint32()).(int32)
		_dafny.Print(_89_integerValue)
		var _90_ret simpletypesintegerinternaldafnytypes.GetIntegerOutput
		_ = _90_ret
		var _91_valueOrError0 Wrappers.Result = Wrappers.Companion_Result_.Default(simpletypesintegerinternaldafnytypes.Companion_GetIntegerOutput_.Default())
		_ = _91_valueOrError0
		var _out5 Wrappers.Result
		_ = _out5
		_out5 = (client).GetInteger(simpletypesintegerinternaldafnytypes.Companion_GetIntegerInput_.Create_GetIntegerInput_(Wrappers.Companion_Option_.Create_Some_(_89_integerValue)))
		_91_valueOrError0 = _out5
		if !(!((_91_valueOrError0).IsFailure())) {
			panic("test/SimpleIntegerImplTest.dfy(53,23): " + (_91_valueOrError0).String())
		}
		_90_ret = (_91_valueOrError0).Extract().(simpletypesintegerinternaldafnytypes.GetIntegerOutput)
		if !((((_90_ret).Dtor_value()).UnwrapOr(int32(0)).(int32)) == (_89_integerValue)) {
			panic("test/SimpleIntegerImplTest.dfy(54,12): " + (_dafny.UnicodeSeqOfUtf8Bytes("expectation violation")).VerbatimString(false))
		}
		_dafny.Print(_90_ret)
	}
}

// End of class Default__
