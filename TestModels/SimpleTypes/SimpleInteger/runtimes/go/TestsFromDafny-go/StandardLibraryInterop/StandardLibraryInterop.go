// Package StandardLibraryInterop
// Dafny module StandardLibraryInterop compiled into Go

package StandardLibraryInterop

import (
	os "os"

	SimpleIntegerImpl "github.com/ShubhamChaturvedi7/SimpleBoolean/SimpleIntegerImpl"
	StandardLibrary "github.com/ShubhamChaturvedi7/SimpleBoolean/StandardLibrary"
	StandardLibrary_UInt "github.com/ShubhamChaturvedi7/SimpleBoolean/StandardLibrary_UInt"
	Wrappers "github.com/ShubhamChaturvedi7/SimpleBoolean/Wrappers"
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

type Dummy__ struct{}

// Definition of class WrappersInterop
type WrappersInterop struct {
	dummy byte
}

func New_WrappersInterop_() *WrappersInterop {
	_this := WrappersInterop{}

	return &_this
}

type CompanionStruct_WrappersInterop_ struct {
}

var Companion_WrappersInterop_ = CompanionStruct_WrappersInterop_{}

func (_this *WrappersInterop) Equals(other *WrappersInterop) bool {
	return _this == other
}

func (_this *WrappersInterop) EqualsGeneric(x interface{}) bool {
	other, ok := x.(*WrappersInterop)
	return ok && _this.Equals(other)
}

func (*WrappersInterop) String() string {
	return "StandardLibraryInterop.WrappersInterop"
}

func Type_WrappersInterop_() _dafny.TypeDescriptor {
	return type_WrappersInterop_{}
}

type type_WrappersInterop_ struct {
}

func (_this type_WrappersInterop_) Default() interface{} {
	return (*WrappersInterop)(nil)
}

func (_this type_WrappersInterop_) String() string {
	return "StandardLibraryInterop.WrappersInterop"
}
func (_this *WrappersInterop) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &WrappersInterop{}

func (_static *CompanionStruct_WrappersInterop_) CreateStringSome(s _dafny.Sequence) Wrappers.Option {
	return Wrappers.Companion_Option_.Create_Some_(s)
}
func (_static *CompanionStruct_WrappersInterop_) CreateStringNone() Wrappers.Option {
	return Wrappers.Companion_Option_.Create_None_()
}
func (_static *CompanionStruct_WrappersInterop_) CreateBooleanSome(b bool) Wrappers.Option {
	return Wrappers.Companion_Option_.Create_Some_(b)
}
func (_static *CompanionStruct_WrappersInterop_) CreateBooleanNone() Wrappers.Option {
	return Wrappers.Companion_Option_.Create_None_()
}

// End of class WrappersInterop
