// Package SimpleResource
// Dafny module SimpleResource compiled into Go

package SimpleResource

import (
	os "os"

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

type Dummy__ struct{}

// Definition of class SimpleResource
type SimpleResource struct {
	_name _dafny.Sequence
}

func New_SimpleResource_() *SimpleResource {
	_this := SimpleResource{}

	_this._name = _dafny.EmptySeq.SetString()
	return &_this
}

type CompanionStruct_SimpleResource_ struct {
}

var Companion_SimpleResource_ = CompanionStruct_SimpleResource_{}

func (_this *SimpleResource) Equals(other *SimpleResource) bool {
	return _this == other
}

func (_this *SimpleResource) EqualsGeneric(x interface{}) bool {
	other, ok := x.(*SimpleResource)
	return ok && _this.Equals(other)
}

func (*SimpleResource) String() string {
	return "SimpleResource.SimpleResource"
}

func Type_SimpleResource_() _dafny.TypeDescriptor {
	return type_SimpleResource_{}
}

type type_SimpleResource_ struct {
}

func (_this type_SimpleResource_) Default() interface{} {
	return (*SimpleResource)(nil)
}

func (_this type_SimpleResource_) String() string {
	return "SimpleResource.SimpleResource"
}
func (_this *SimpleResource) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){simplepositionalinternaldafnytypes.Companion_ISimpleResource_.TraitID_}
}

var _ simplepositionalinternaldafnytypes.ISimpleResource = &SimpleResource{}
var _ _dafny.TraitOffspring = &SimpleResource{}

func (_this *SimpleResource) GetName(input simplepositionalinternaldafnytypes.GetNameInput) Wrappers.Result {
	var _out1 Wrappers.Result
	_ = _out1
	_out1 = simplepositionalinternaldafnytypes.Companion_ISimpleResource_.GetName(_this, input)
	return _out1
}
func (_this *SimpleResource) Ctor__(name _dafny.Sequence) {
	{
		(_this)._name = name
	}
}
func (_this *SimpleResource) GetName_k(input simplepositionalinternaldafnytypes.GetNameInput) Wrappers.Result {
	{
		var output Wrappers.Result = Wrappers.Companion_Result_.Default(simplepositionalinternaldafnytypes.Companion_GetNameOutput_.Default())
		_ = output
		output = Wrappers.Companion_Result_.Create_Success_(simplepositionalinternaldafnytypes.Companion_GetNameOutput_.Create_GetNameOutput_((_this).Name()))
		return output
		return output
	}
}
func (_this *SimpleResource) Name() _dafny.Sequence {
	{
		return _this._name
	}
}

// End of class SimpleResource
