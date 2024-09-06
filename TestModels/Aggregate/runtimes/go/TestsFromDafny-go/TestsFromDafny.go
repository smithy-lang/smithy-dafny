// Dafny program the_program compiled into Go
package main

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
	WrappedSimpleTypesStringTest "github.com/smithy-lang/smithy-dafny/TestModels/Aggregate/test/WrappedSimpleTypesStringTest"
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
var _ WrappedSimpleTypesStringTest.Dummy__

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
	var _18_success bool
	_ = _18_success
	_18_success = true
	_dafny.Print((_dafny.SeqOfString("SimpleAggregateImplTest.GetAggregate: ")).SetString())
	func() {
		defer func() {
			if r := recover(); r != nil {
				var _19_haltMessage = _dafny.SeqOfString(r.(string))
				{
					_dafny.Print((_dafny.SeqOfString("FAILED\n	")).SetString())
					_dafny.Print((_19_haltMessage).SetString())
					_dafny.Print((_dafny.SeqOfString("\n")).SetString())
					_18_success = false
				}
			}
		}()
		{
			SimpleAggregateImplTest.Companion_Default___.GetAggregate()
			{
				_dafny.Print((_dafny.SeqOfString("PASSED\n")).SetString())
			}
		}
	}()
	_dafny.Print((_dafny.SeqOfString("WrappedSimpleTypesStringTest.GetAggregate: ")).SetString())
	func() {
		defer func() {
			if r := recover(); r != nil {
				var _20_haltMessage = _dafny.SeqOfString(r.(string))
				{
					_dafny.Print((_dafny.SeqOfString("FAILED\n	")).SetString())
					_dafny.Print((_20_haltMessage).SetString())
					_dafny.Print((_dafny.SeqOfString("\n")).SetString())
					_18_success = false
				}
			}
		}()
		{
			WrappedSimpleTypesStringTest.Companion_Default___.GetAggregate()
			{
				_dafny.Print((_dafny.SeqOfString("PASSED\n")).SetString())
			}
		}
	}()
	if !(_18_success) {
		panic("<stdin>(1,0): " + (_dafny.SeqOfString("Test failures occurred: see above.\n")).String())
	}
}

// End of class Default__
func main() {
	defer _dafny.CatchHalt()
	Companion_Default___.Test____Main____(_dafny.FromMainArguments(os.Args))
}
