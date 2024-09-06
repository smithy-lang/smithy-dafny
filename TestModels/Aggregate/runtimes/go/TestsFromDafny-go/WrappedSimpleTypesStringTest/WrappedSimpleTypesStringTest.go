// Package WrappedSimpleTypesStringTest
// Dafny module WrappedSimpleTypesStringTest compiled into Go

package WrappedSimpleTypesStringTest

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
	SimpleAggregateImplTest "github.com/smithy-lang/smithy-dafny/TestModels/Aggregate/test/SimpleAggregateImplTest"
	WrappedSimpleAggregateService "github.com/smithy-lang/smithy-dafny/TestModels/Aggregate/test/WrappedSimpleAggregateService"
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
var _ SimpleAggregateImplTest.Dummy__
var _ WrappedSimpleAggregateService.Dummy__

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
	return "WrappedSimpleTypesStringTest.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) GetAggregate() {
	var _16_client SimpleAggregateTypes.ISimpleAggregateClient
	_ = _16_client
	var _17_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _17_valueOrError0
	var _out3 Wrappers.Result
	_ = _out3
	_out3 = WrappedSimpleAggregateService.Companion_Default___.WrappedSimpleAggregate(WrappedSimpleAggregateService.Companion_Default___.WrappedDefaultSimpleAggregateConfig())
	_17_valueOrError0 = _out3
	if !(!((_17_valueOrError0).IsFailure())) {
		panic("test/WrappedSimpleAggregateImplTest.dfy(11,22): " + (_17_valueOrError0).String())
	}
	_16_client = SimpleAggregateTypes.Companion_ISimpleAggregateClient_.CastTo_((_17_valueOrError0).Extract())
	SimpleAggregateImplTest.Companion_Default___.TestGetAggregate(_16_client)
	SimpleAggregateImplTest.Companion_Default___.TestGetAggregateKnownValue(_16_client)
}

// End of class Default__
