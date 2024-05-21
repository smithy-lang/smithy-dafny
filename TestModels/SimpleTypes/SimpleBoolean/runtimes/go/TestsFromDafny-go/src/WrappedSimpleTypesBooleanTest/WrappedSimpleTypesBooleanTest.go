// Package WrappedSimpleTypesBooleanTest
// Dafny module WrappedSimpleTypesBooleanTest compiled into Go

package WrappedSimpleTypesBooleanTest

import (
	SimpleBooleanImpl "SimpleBooleanImpl"
	SimpleBooleanImplTest "SimpleBooleanImplTest"
	StandardLibrary "StandardLibrary"
	StandardLibrary_mUInt "StandardLibrary_mUInt"
	_System "System_"
	Wrappers "Wrappers"
	_dafny "dafny"
	os "os"
	simpletypesbooleaninternaldafnytypes "simpletypesbooleaninternaldafnytypes"
	simpletypesbooleaninternaldafnywrapped "simpletypesbooleaninternaldafnywrapped"
)

var _ _dafny.Dummy__
var _ = os.Args
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_mUInt.Dummy__
var _ StandardLibrary.Dummy__
var _ SimpleBooleanImpl.Dummy__
var _ SimpleBooleanImplTest.Dummy__

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
	return "WrappedSimpleTypesBooleanTest.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) GetBooleanTrue() {
	var _82_client simpletypesbooleaninternaldafnytypes.ISimpleTypesBooleanClient
	_ = _82_client
	var _83_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _83_valueOrError0
	var _out5 Wrappers.Result
	_ = _out5
	_out5 = simpletypesbooleaninternaldafnywrapped.WrappedSimpleBoolean(simpletypesbooleaninternaldafnywrapped.Companion_Default___.WrappedDefaultSimpleBooleanConfig())
	_83_valueOrError0 = _out5
	if !(!((_83_valueOrError0).IsFailure())) {
		panic("test/WrappedSimpleBooleanTest.dfy(11,19): " + (_83_valueOrError0).String())
	}
	_82_client = simpletypesbooleaninternaldafnytypes.Companion_ISimpleTypesBooleanClient_.CastTo_((_83_valueOrError0).Extract())
	SimpleBooleanImplTest.Companion_Default___.TestGetBooleanTrue(_82_client)
}
func (_static *CompanionStruct_Default___) GetBooleanFalse() {
	var _84_client simpletypesbooleaninternaldafnytypes.ISimpleTypesBooleanClient
	_ = _84_client
	var _85_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _85_valueOrError0
	var _out6 Wrappers.Result
	_ = _out6
	_out6 = simpletypesbooleaninternaldafnywrapped.WrappedSimpleBoolean(simpletypesbooleaninternaldafnywrapped.Companion_Default___.WrappedDefaultSimpleBooleanConfig())
	_85_valueOrError0 = _out6
	if !(!((_85_valueOrError0).IsFailure())) {
		panic("test/WrappedSimpleBooleanTest.dfy(15,19): " + (_85_valueOrError0).String())
	}
	_84_client = simpletypesbooleaninternaldafnytypes.Companion_ISimpleTypesBooleanClient_.CastTo_((_85_valueOrError0).Extract())
	SimpleBooleanImplTest.Companion_Default___.TestGetBooleanFalse(_84_client)
}

// End of class Default__
