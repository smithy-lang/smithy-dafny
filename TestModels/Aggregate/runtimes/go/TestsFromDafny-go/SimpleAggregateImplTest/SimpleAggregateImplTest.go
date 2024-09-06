// Package SimpleAggregateImplTest
// Dafny module SimpleAggregateImplTest compiled into Go

package SimpleAggregateImplTest

import (
	os "os"

	SimpleAggregate "github.com/smithy-lang/smithy-dafny/TestModels/Aggregate/SimpleAggregate"
	SimpleAggregateImpl "github.com/smithy-lang/smithy-dafny/TestModels/Aggregate/SimpleAggregateImpl"
	SimpleAggregateTypes "github.com/smithy-lang/smithy-dafny/TestModels/Aggregate/SimpleAggregateTypes"

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
var _ SimpleAggregateTypes.Dummy__
var _ SimpleAggregateImpl.Dummy__
var _ SimpleAggregate.Dummy__
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
	return "SimpleAggregateImplTest.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) GetAggregate() {
	var _0_client *SimpleAggregate.SimpleAggregateClient
	_ = _0_client
	var _1_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _1_valueOrError0
	var _out0 Wrappers.Result
	_ = _out0
	_out0 = SimpleAggregate.Companion_Default___.SimpleAggregate(SimpleAggregate.Companion_Default___.DefaultSimpleAggregateConfig())
	_1_valueOrError0 = _out0
	if !(!((_1_valueOrError0).IsFailure())) {
		panic("test/SimpleAggregateImplTest.dfy(10,22): " + (_1_valueOrError0).String())
	}
	_0_client = (_1_valueOrError0).Extract().(*SimpleAggregate.SimpleAggregateClient)
	Companion_Default___.TestGetAggregate(_0_client)
	Companion_Default___.TestGetAggregateKnownValue(_0_client)
}
func (_static *CompanionStruct_Default___) TestGetAggregate(client SimpleAggregateTypes.ISimpleAggregateClient) {
	var _2_stringList _dafny.Sequence
	_ = _2_stringList
	_2_stringList = _dafny.SeqOf(_dafny.SeqOfString("Test"))
	var _3_simpleStringMap _dafny.Map
	_ = _3_simpleStringMap
	_3_simpleStringMap = _dafny.NewMapBuilder().ToMap().UpdateUnsafe(_dafny.SeqOfString("Test1"), _dafny.SeqOfString("Success"))
	var _4_structureList _dafny.Sequence
	_ = _4_structureList
	_4_structureList = _dafny.SeqOf(SimpleAggregateTypes.Companion_StructureListElement_.Create_StructureListElement_(Wrappers.Companion_Option_.Create_Some_(_dafny.SeqOfString("Test2")), Wrappers.Companion_Option_.Create_Some_(int32(2))))
	var _5_simpleIntegerMap _dafny.Map
	_ = _5_simpleIntegerMap
	_5_simpleIntegerMap = _dafny.NewMapBuilder().ToMap().UpdateUnsafe(_dafny.SeqOfString("Test3"), int32(3))
	var _6_nestedStructure SimpleAggregateTypes.NestedStructure
	_ = _6_nestedStructure
	_6_nestedStructure = SimpleAggregateTypes.Companion_NestedStructure_.Create_NestedStructure_(Wrappers.Companion_Option_.Create_Some_(SimpleAggregateTypes.Companion_StringStructure_.Create_StringStructure_(Wrappers.Companion_Option_.Create_Some_(_dafny.SeqOfString("Nested")))))
	var _7_ret SimpleAggregateTypes.GetAggregateOutput
	_ = _7_ret
	var _8_valueOrError0 Wrappers.Result = Wrappers.Companion_Result_.Default(SimpleAggregateTypes.Companion_GetAggregateOutput_.Default())
	_ = _8_valueOrError0
	var _out1 Wrappers.Result
	_ = _out1
	_out1 = (client).GetAggregate(SimpleAggregateTypes.Companion_GetAggregateInput_.Create_GetAggregateInput_(Wrappers.Companion_Option_.Create_Some_(_2_stringList), Wrappers.Companion_Option_.Create_Some_(_4_structureList), Wrappers.Companion_Option_.Create_Some_(_3_simpleStringMap), Wrappers.Companion_Option_.Create_Some_(_5_simpleIntegerMap), Wrappers.Companion_Option_.Create_Some_(_6_nestedStructure)))
	_8_valueOrError0 = _out1
	if !(!((_8_valueOrError0).IsFailure())) {
		panic("test/SimpleAggregateImplTest.dfy(25,19): " + (_8_valueOrError0).String())
	}
	_7_ret = (_8_valueOrError0).Extract().(SimpleAggregateTypes.GetAggregateOutput)
	if !(_dafny.Companion_Sequence_.Equal(((_7_ret).Dtor_simpleStringList()).UnwrapOr(_dafny.SeqOf()).(_dafny.Sequence), _2_stringList)) {
		panic("test/SimpleAggregateImplTest.dfy(31,8): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	if !(_dafny.Companion_Sequence_.Equal(((_7_ret).Dtor_structureList()).UnwrapOr(_dafny.SeqOf()).(_dafny.Sequence), _4_structureList)) {
		panic("test/SimpleAggregateImplTest.dfy(32,8): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	if !((((_7_ret).Dtor_simpleStringMap()).UnwrapOr(_dafny.NewMapBuilder().ToMap()).(_dafny.Map)).Equals(_3_simpleStringMap)) {
		panic("test/SimpleAggregateImplTest.dfy(33,8): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	if !((((_7_ret).Dtor_simpleIntegerMap()).UnwrapOr(_dafny.NewMapBuilder().ToMap()).(_dafny.Map)).Equals(_5_simpleIntegerMap)) {
		panic("test/SimpleAggregateImplTest.dfy(34,8): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	if !((((_7_ret).Dtor_nestedStructure()).UnwrapOr(SimpleAggregateTypes.Companion_NestedStructure_.Create_NestedStructure_(Wrappers.Companion_Option_.Create_Some_(SimpleAggregateTypes.Companion_StringStructure_.Create_StringStructure_(Wrappers.Companion_Option_.Create_Some_(_dafny.SeqOfString("")))))).(SimpleAggregateTypes.NestedStructure)).Equals(_6_nestedStructure)) {
		panic("test/SimpleAggregateImplTest.dfy(35,8): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	_dafny.Print(_7_ret)
}
func (_static *CompanionStruct_Default___) TestGetAggregateKnownValue(client SimpleAggregateTypes.ISimpleAggregateClient) {
	var _9_stringList _dafny.Sequence
	_ = _9_stringList
	_9_stringList = _dafny.SeqOf(_dafny.SeqOfString("Test"))
	var _10_simpleStringMap _dafny.Map
	_ = _10_simpleStringMap
	_10_simpleStringMap = _dafny.NewMapBuilder().ToMap().UpdateUnsafe(_dafny.SeqOfString("Test1"), _dafny.SeqOfString("Success"))
	var _11_structureList _dafny.Sequence
	_ = _11_structureList
	_11_structureList = _dafny.SeqOf(SimpleAggregateTypes.Companion_StructureListElement_.Create_StructureListElement_(Wrappers.Companion_Option_.Create_Some_(_dafny.SeqOfString("Test2")), Wrappers.Companion_Option_.Create_Some_(int32(2))))
	var _12_simpleIntegerMap _dafny.Map
	_ = _12_simpleIntegerMap
	_12_simpleIntegerMap = _dafny.NewMapBuilder().ToMap().UpdateUnsafe(_dafny.SeqOfString("Test3"), int32(3))
	var _13_nestedStructure SimpleAggregateTypes.NestedStructure
	_ = _13_nestedStructure
	_13_nestedStructure = SimpleAggregateTypes.Companion_NestedStructure_.Create_NestedStructure_(Wrappers.Companion_Option_.Create_Some_(SimpleAggregateTypes.Companion_StringStructure_.Create_StringStructure_(Wrappers.Companion_Option_.Create_Some_(_dafny.SeqOfString("Nested")))))
	var _14_ret SimpleAggregateTypes.GetAggregateOutput
	_ = _14_ret
	var _15_valueOrError0 Wrappers.Result = Wrappers.Companion_Result_.Default(SimpleAggregateTypes.Companion_GetAggregateOutput_.Default())
	_ = _15_valueOrError0
	var _out2 Wrappers.Result
	_ = _out2
	_out2 = (client).GetAggregate(SimpleAggregateTypes.Companion_GetAggregateInput_.Create_GetAggregateInput_(Wrappers.Companion_Option_.Create_Some_(_9_stringList), Wrappers.Companion_Option_.Create_Some_(_11_structureList), Wrappers.Companion_Option_.Create_Some_(_10_simpleStringMap), Wrappers.Companion_Option_.Create_Some_(_12_simpleIntegerMap), Wrappers.Companion_Option_.Create_Some_(_13_nestedStructure)))
	_15_valueOrError0 = _out2
	if !(!((_15_valueOrError0).IsFailure())) {
		panic("test/SimpleAggregateImplTest.dfy(49,19): " + (_15_valueOrError0).String())
	}
	_14_ret = (_15_valueOrError0).Extract().(SimpleAggregateTypes.GetAggregateOutput)
	if !(_dafny.Companion_Sequence_.Equal(((_14_ret).Dtor_simpleStringList()).UnwrapOr(_dafny.SeqOf()).(_dafny.Sequence), _9_stringList)) {
		panic("test/SimpleAggregateImplTest.dfy(55,8): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	if !(_dafny.Companion_Sequence_.Equal(((_14_ret).Dtor_structureList()).UnwrapOr(_dafny.SeqOf()).(_dafny.Sequence), _11_structureList)) {
		panic("test/SimpleAggregateImplTest.dfy(56,8): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	if !((((_14_ret).Dtor_simpleStringMap()).UnwrapOr(_dafny.NewMapBuilder().ToMap()).(_dafny.Map)).Equals(_10_simpleStringMap)) {
		panic("test/SimpleAggregateImplTest.dfy(57,8): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	if !((((_14_ret).Dtor_simpleIntegerMap()).UnwrapOr(_dafny.NewMapBuilder().ToMap()).(_dafny.Map)).Equals(_12_simpleIntegerMap)) {
		panic("test/SimpleAggregateImplTest.dfy(58,8): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	if !((((_14_ret).Dtor_nestedStructure()).UnwrapOr(SimpleAggregateTypes.Companion_NestedStructure_.Create_NestedStructure_(Wrappers.Companion_Option_.Create_Some_(SimpleAggregateTypes.Companion_StringStructure_.Create_StringStructure_(Wrappers.Companion_Option_.Create_Some_(_dafny.SeqOfString("")))))).(SimpleAggregateTypes.NestedStructure)).Equals(_13_nestedStructure)) {
		panic("test/SimpleAggregateImplTest.dfy(59,8): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	_dafny.Print(_14_ret)
}

// End of class Default__
