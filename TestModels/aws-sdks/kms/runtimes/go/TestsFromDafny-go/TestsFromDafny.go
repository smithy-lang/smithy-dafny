// Dafny program the_program compiled into Go
package main

import (
	os "os"

	Com "github.com/smithy-lang/smithy-dafny/kms/Com"
	ComAmazonawsKmsTypes "github.com/smithy-lang/smithy-dafny/kms/ComAmazonawsKmsTypes"
	Com_Amazonaws "github.com/smithy-lang/smithy-dafny/kms/Com_Amazonaws"
	Com_Amazonaws_Kms "github.com/smithy-lang/smithy-dafny/kms/Com_Amazonaws_Kms"

	_System "github.com/dafny-lang/DafnyRuntimeGo/System_"
	_dafny "github.com/dafny-lang/DafnyRuntimeGo/dafny"
	StandardLibrary "github.com/dafny-lang/DafnyStandardLibGo/StandardLibrary"
	StandardLibraryInterop "github.com/dafny-lang/DafnyStandardLibGo/StandardLibraryInterop"
	StandardLibrary_UInt "github.com/dafny-lang/DafnyStandardLibGo/StandardLibrary_UInt"
	Wrappers "github.com/dafny-lang/DafnyStandardLibGo/Wrappers"
	TestComAmazonawsKms "github.com/smithy-lang/smithy-dafny/kms/TestComAmazonawsKms"
)

var _ = os.Args
var _ _dafny.Dummy__
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_UInt.Dummy__
var _ StandardLibrary.Dummy__
var _ ComAmazonawsKmsTypes.Dummy__
var _ StandardLibraryInterop.Dummy__
var _ Com_Amazonaws_Kms.Dummy__
var _ Com_Amazonaws.Dummy__
var _ Com.Dummy__
var _ TestComAmazonawsKms.Dummy__

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
	var _26_success bool
	_ = _26_success
	_26_success = true
	_dafny.Print((_dafny.SeqOfString("TestComAmazonawsKms.BasicDecryptTests: ")).SetString())
	func() {
		defer func() {
			if r := recover(); r != nil {
				var _27_haltMessage = _dafny.SeqOfString(r.(string))
				{
					_dafny.Print((_dafny.SeqOfString("FAILED\n	")).SetString())
					_dafny.Print((_27_haltMessage).SetString())
					_dafny.Print((_dafny.SeqOfString("\n")).SetString())
					_26_success = false
				}
			}
		}()
		{
			TestComAmazonawsKms.Companion_Default___.BasicDecryptTests()
			{
				_dafny.Print((_dafny.SeqOfString("PASSED\n")).SetString())
			}
		}
	}()
	_dafny.Print((_dafny.SeqOfString("TestComAmazonawsKms.BasicGenerateTests: ")).SetString())
	func() {
		defer func() {
			if r := recover(); r != nil {
				var _28_haltMessage = _dafny.SeqOfString(r.(string))
				{
					_dafny.Print((_dafny.SeqOfString("FAILED\n	")).SetString())
					_dafny.Print((_28_haltMessage).SetString())
					_dafny.Print((_dafny.SeqOfString("\n")).SetString())
					_26_success = false
				}
			}
		}()
		{
			TestComAmazonawsKms.Companion_Default___.BasicGenerateTests()
			{
				_dafny.Print((_dafny.SeqOfString("PASSED\n")).SetString())
			}
		}
	}()
	_dafny.Print((_dafny.SeqOfString("TestComAmazonawsKms.BasicEncryptTests: ")).SetString())
	func() {
		defer func() {
			if r := recover(); r != nil {
				var _29_haltMessage = _dafny.SeqOfString(r.(string))
				{
					_dafny.Print((_dafny.SeqOfString("FAILED\n	")).SetString())
					_dafny.Print((_29_haltMessage).SetString())
					_dafny.Print((_dafny.SeqOfString("\n")).SetString())
					_26_success = false
				}
			}
		}()
		{
			TestComAmazonawsKms.Companion_Default___.BasicEncryptTests()
			{
				_dafny.Print((_dafny.SeqOfString("PASSED\n")).SetString())
			}
		}
	}()
	_dafny.Print((_dafny.SeqOfString("TestComAmazonawsKms.RegionMatchTest: ")).SetString())
	func() {
		defer func() {
			if r := recover(); r != nil {
				var _30_haltMessage = _dafny.SeqOfString(r.(string))
				{
					_dafny.Print((_dafny.SeqOfString("FAILED\n	")).SetString())
					_dafny.Print((_30_haltMessage).SetString())
					_dafny.Print((_dafny.SeqOfString("\n")).SetString())
					_26_success = false
				}
			}
		}()
		{
			TestComAmazonawsKms.Companion_Default___.RegionMatchTest()
			{
				_dafny.Print((_dafny.SeqOfString("PASSED\n")).SetString())
			}
		}
	}()
	if !(_26_success) {
		panic("<stdin>(1,0): " + (_dafny.SeqOfString("Test failures occurred: see above.\n")).String())
	}
}

// End of class Default__
func main() {
	defer _dafny.CatchHalt()
	Companion_Default___.Test____Main____(_dafny.FromMainArguments(os.Args))
}
