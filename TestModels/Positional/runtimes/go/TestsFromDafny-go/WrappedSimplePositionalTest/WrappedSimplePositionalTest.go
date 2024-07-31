// Package WrappedSimplePositionalTest
// Dafny module WrappedSimplePositionalTest compiled into Go

package WrappedSimplePositionalTest

import (
	os "os"

	SimplePositionalImpl "github.com/Smithy-dafny/TestModels/Positional/SimplePositionalImpl"
	SimplePositionalImplTest "github.com/Smithy-dafny/TestModels/Positional/SimplePositionalImplTest"
	SimpleResource "github.com/Smithy-dafny/TestModels/Positional/SimpleResource"
	simplepositionalinternaldafnytypes "github.com/Smithy-dafny/TestModels/Positional/simplepositionalinternaldafnytypes"
	simplepositionalinternaldafnywrapped "github.com/Smithy-dafny/TestModels/Positional/simplepositionalinternaldafnywrapped"
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
var _ SimplePositionalImplTest.Dummy__

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
	return "WrappedSimplePositionalTest.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) TestWrappedClient() {
	var _18_client simplepositionalinternaldafnytypes.ISimplePositionalClient
	_ = _18_client
	var _19_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _19_valueOrError0
	var _out9 Wrappers.Result
	_ = _out9
	_out9 = simplepositionalinternaldafnywrapped.WrappedSimplePositional(simplepositionalinternaldafnywrapped.Companion_Default___.WrappedDefaultSimplePositionalConfig())
	_19_valueOrError0 = _out9
	if !(!((_19_valueOrError0).IsFailure())) {
		panic("test/WrappedSimplePositionalTest.dfy(12,22): " + (_19_valueOrError0).String())
	}
	_18_client = simplepositionalinternaldafnytypes.Companion_ISimplePositionalClient_.CastTo_((_19_valueOrError0).Extract())
	SimplePositionalImplTest.Companion_Default___.TestClient(_18_client)
}

// End of class Default__
