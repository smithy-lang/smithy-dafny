// Package WrappedSimpleTypesIntegerTest
// Dafny module WrappedSimpleTypesIntegerTest compiled into Go

package WrappedSimpleTypesIntegerTest

import (
	os "os"

	SimpleIntegerImpl "github.com/ShubhamChaturvedi7/SimpleBoolean/SimpleIntegerImpl"
	SimpleIntegerImplTest "github.com/ShubhamChaturvedi7/SimpleBoolean/SimpleIntegerImplTest"
	StandardLibrary "github.com/ShubhamChaturvedi7/SimpleBoolean/StandardLibrary"
	StandardLibraryInterop "github.com/ShubhamChaturvedi7/SimpleBoolean/StandardLibraryInterop"
	StandardLibrary_UInt "github.com/ShubhamChaturvedi7/SimpleBoolean/StandardLibrary_UInt"
	Wrappers "github.com/ShubhamChaturvedi7/SimpleBoolean/Wrappers"
	simpletypesintegerinternaldafnytypes "github.com/ShubhamChaturvedi7/SimpleBoolean/simpletypesintegerinternaldafnytypes"
	simpletypesintegerinternaldafnywrapped "github.com/ShubhamChaturvedi7/SimpleBoolean/simpletypesintegerinternaldafnywrapped"
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
var _ SimpleIntegerImplTest.Dummy__

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
	return "WrappedSimpleTypesIntegerTest.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) GetInteger() {
	var _92_client simpletypesintegerinternaldafnytypes.ISimpleTypesIntegerClient
	_ = _92_client
	var _93_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _93_valueOrError0
	var _out6 Wrappers.Result
	_ = _out6
	_out6 = simpletypesintegerinternaldafnywrapped.WrappedSimpleInteger(simpletypesintegerinternaldafnywrapped.Companion_Default___.WrappedDefaultSimpleIntegerConfig())
	_93_valueOrError0 = _out6
	if !(!((_93_valueOrError0).IsFailure())) {
		panic("test/WrappedSimpleIntegerTest.dfy(11,22): " + (_93_valueOrError0).String())
	}
	_92_client = simpletypesintegerinternaldafnytypes.Companion_ISimpleTypesIntegerClient_.CastTo_((_93_valueOrError0).Extract())
	SimpleIntegerImplTest.Companion_Default___.TestGetInteger(_92_client)
	SimpleIntegerImplTest.Companion_Default___.TestGetIntegerKnownValue(_92_client)
	SimpleIntegerImplTest.Companion_Default___.TestGetIntegerEdgeCases(_92_client)
}

// End of class Default__
