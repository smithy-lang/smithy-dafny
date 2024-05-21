// Dafny program <stdin> compiled into Go
package main

import (
	os "os"

	SimpleIntegerImpl "github.com/ShubhamChaturvedi7/SimpleBoolean/SimpleIntegerImpl"
	SimpleIntegerImplTest "github.com/ShubhamChaturvedi7/SimpleBoolean/SimpleIntegerImplTest"
	StandardLibrary "github.com/ShubhamChaturvedi7/SimpleBoolean/StandardLibrary"
	StandardLibraryInterop "github.com/ShubhamChaturvedi7/SimpleBoolean/StandardLibraryInterop"
	StandardLibrary_UInt "github.com/ShubhamChaturvedi7/SimpleBoolean/StandardLibrary_UInt"
	WrappedSimpleTypesIntegerTest "github.com/ShubhamChaturvedi7/SimpleBoolean/WrappedSimpleTypesIntegerTest"
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
var _ StandardLibraryInterop.Dummy__
var _ SimpleIntegerImplTest.Dummy__
var _ WrappedSimpleTypesIntegerTest.Dummy__

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
	var _94_success bool
	_ = _94_success
	_94_success = true
	_dafny.Print(_dafny.UnicodeSeqOfUtf8Bytes("SimpleIntegerImplTest.GetInteger: ").VerbatimString(false))
	func() {
		defer func() {
			if r := recover(); r != nil {
				var _95_haltMessage = _dafny.UnicodeSeqOfUtf8Bytes(r.(string))
				{
					_dafny.Print(_dafny.UnicodeSeqOfUtf8Bytes("FAILED\n	").VerbatimString(false))
					_dafny.Print(_95_haltMessage.VerbatimString(false))
					_dafny.Print(_dafny.UnicodeSeqOfUtf8Bytes("\n").VerbatimString(false))
					_94_success = false
				}
			}
		}()
		{
			SimpleIntegerImplTest.Companion_Default___.GetInteger()
			{
				_dafny.Print(_dafny.UnicodeSeqOfUtf8Bytes("PASSED\n").VerbatimString(false))
			}
		}
	}()
	_dafny.Print(_dafny.UnicodeSeqOfUtf8Bytes("WrappedSimpleTypesIntegerTest.GetInteger: ").VerbatimString(false))
	func() {
		defer func() {
			if r := recover(); r != nil {
				var _96_haltMessage = _dafny.UnicodeSeqOfUtf8Bytes(r.(string))
				{
					_dafny.Print(_dafny.UnicodeSeqOfUtf8Bytes("FAILED\n	").VerbatimString(false))
					_dafny.Print(_96_haltMessage.VerbatimString(false))
					_dafny.Print(_dafny.UnicodeSeqOfUtf8Bytes("\n").VerbatimString(false))
					_94_success = false
				}
			}
		}()
		{
			WrappedSimpleTypesIntegerTest.Companion_Default___.GetInteger()
			{
				_dafny.Print(_dafny.UnicodeSeqOfUtf8Bytes("PASSED\n").VerbatimString(false))
			}
		}
	}()
	if !(_94_success) {
		panic("<stdin>(1,0): " + (_dafny.UnicodeSeqOfUtf8Bytes("Test failures occurred: see above.\n")).VerbatimString(false))
	}
}

// End of class Default__
func main() {
	defer _dafny.CatchHalt()
	Companion_Default___.Test____Main____(_dafny.UnicodeFromMainArguments(os.Args))
}
