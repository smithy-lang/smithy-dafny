// Package simpletypesintegerinternaldafnywrapped
// Dafny module simpletypesintegerinternaldafnywrapped compiled into Go

package simpletypesintegerinternaldafnywrapped

import (
	os "os"

	SimpleIntegerImpl "github.com/ShubhamChaturvedi7/SimpleBoolean/SimpleIntegerImpl"
	StandardLibrary "github.com/ShubhamChaturvedi7/SimpleBoolean/StandardLibrary"
	StandardLibraryInterop "github.com/ShubhamChaturvedi7/SimpleBoolean/StandardLibraryInterop"
	StandardLibrary_UInt "github.com/ShubhamChaturvedi7/SimpleBoolean/StandardLibrary_UInt"
	Wrappers "github.com/ShubhamChaturvedi7/SimpleBoolean/Wrappers"
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
	return "simpletypesintegerinternaldafnywrapped.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) WrappedDefaultSimpleIntegerConfig() simpletypesintegerinternaldafnytypes.SimpleIntegerConfig {
	return simpletypesintegerinternaldafnytypes.Companion_SimpleIntegerConfig_.Create_SimpleIntegerConfig_()
}

// End of class Default__
