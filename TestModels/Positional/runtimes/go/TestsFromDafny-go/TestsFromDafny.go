// Dafny program the_program compiled into Go
package main

import (
	os "os"

	SimplePositionalImpl "github.com/Smithy-dafny/TestModels/Positional/SimplePositionalImpl"
	SimplePositionalImplTest "github.com/Smithy-dafny/TestModels/Positional/SimplePositionalImplTest"
	SimpleResource "github.com/Smithy-dafny/TestModels/Positional/SimpleResource"
	WrappedSimplePositionalTest "github.com/Smithy-dafny/TestModels/Positional/WrappedSimplePositionalTest"
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
var _ WrappedSimplePositionalTest.Dummy__

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
	return "_module.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) Test____Main____(__noArgsParameter _dafny.Sequence) {
	var _20_success bool
	_ = _20_success
	_20_success = true
	_dafny.Print((_dafny.SeqOfString("SimplePositionalImplTest.TestDefaultConfig: ")).SetString())
	func() {
		defer func() {
			if r := recover(); r != nil {
				var _21_haltMessage = _dafny.SeqOfString(r.(string))
				{
					_dafny.Print((_dafny.SeqOfString("FAILED\n	")).SetString())
					_dafny.Print((_21_haltMessage).SetString())
					_dafny.Print((_dafny.SeqOfString("\n")).SetString())
					_20_success = false
				}
			}
		}()
		{
			SimplePositionalImplTest.Companion_Default___.TestDefaultConfig()
			{
				_dafny.Print((_dafny.SeqOfString("PASSED\n")).SetString())
			}
		}
	}()
	_dafny.Print((_dafny.SeqOfString("WrappedSimplePositionalTest.TestWrappedClient: ")).SetString())
	func() {
		defer func() {
			if r := recover(); r != nil {
				var _22_haltMessage = _dafny.SeqOfString(r.(string))
				{
					_dafny.Print((_dafny.SeqOfString("FAILED\n	")).SetString())
					_dafny.Print((_22_haltMessage).SetString())
					_dafny.Print((_dafny.SeqOfString("\n")).SetString())
					_20_success = false
				}
			}
		}()
		{
			WrappedSimplePositionalTest.Companion_Default___.TestWrappedClient()
			{
				_dafny.Print((_dafny.SeqOfString("PASSED\n")).SetString())
			}
		}
	}()
	if !(_20_success) {
		panic("<stdin>(1,0): " + (_dafny.SeqOfString("Test failures occurred: see above.\n")).String())
	}
}

// End of class Default__
func main() {
	defer _dafny.CatchHalt()
	Companion_Default___.Test____Main____(_dafny.FromMainArguments(os.Args))
}
