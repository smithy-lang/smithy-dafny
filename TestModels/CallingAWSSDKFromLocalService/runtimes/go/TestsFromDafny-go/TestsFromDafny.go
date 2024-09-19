// Dafny program the_program compiled into Go
package main

import (
	os "os"

	_System "github.com/dafny-lang/DafnyRuntimeGo/System_"
	_dafny "github.com/dafny-lang/DafnyRuntimeGo/dafny"
	StandardLibrary "github.com/dafny-lang/DafnyStandardLibGo/StandardLibrary"
	StandardLibraryInterop "github.com/dafny-lang/DafnyStandardLibGo/StandardLibraryInterop"
	StandardLibrary_UInt "github.com/dafny-lang/DafnyStandardLibGo/StandardLibrary_UInt"
	Wrappers "github.com/dafny-lang/DafnyStandardLibGo/Wrappers"
	SimpleCallingAWSSDKFromLocalService "github.com/smithy-lang/smithy-dafny/TestModels/CallingAWSSDKFromLocalService/SimpleCallingAWSSDKFromLocalService"
	SimpleCallingAWSSDKFromLocalServiceImpl "github.com/smithy-lang/smithy-dafny/TestModels/CallingAWSSDKFromLocalService/SimpleCallingAWSSDKFromLocalServiceImpl"
	SimpleCallingawssdkfromlocalserviceTypes "github.com/smithy-lang/smithy-dafny/TestModels/CallingAWSSDKFromLocalService/SimpleCallingawssdkfromlocalserviceTypes"
	SimpleCallingAWSSDKFromLocalServiceImplTest "github.com/smithy-lang/smithy-dafny/TestModels/CallingAWSSDKFromLocalService/test/SimpleCallingAWSSDKFromLocalServiceImplTest"
	WrappedSimpleCallingAWSSDKFromLocalServiceService "github.com/smithy-lang/smithy-dafny/TestModels/CallingAWSSDKFromLocalService/test/WrappedSimpleCallingAWSSDKFromLocalServiceService"
	WrappedSimpleCallingAWSSDKFromLocalServiceTest "github.com/smithy-lang/smithy-dafny/TestModels/CallingAWSSDKFromLocalService/test/WrappedSimpleCallingAWSSDKFromLocalServiceTest"
	ComAmazonawsKmsTypes "github.com/smithy-lang/smithy-dafny/kms/ComAmazonawsKmsTypes"
	Com_Amazonaws_Kms "github.com/smithy-lang/smithy-dafny/kms/Com_Amazonaws_Kms"
)

var _ = os.Args
var _ _dafny.Dummy__
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_UInt.Dummy__
var _ StandardLibrary.Dummy__
var _ ComAmazonawsKmsTypes.Dummy__
var _ SimpleCallingawssdkfromlocalserviceTypes.Dummy__
var _ Com_Amazonaws_Kms.Dummy__
var _ SimpleCallingAWSSDKFromLocalServiceImpl.Dummy__
var _ SimpleCallingAWSSDKFromLocalService.Dummy__
var _ StandardLibraryInterop.Dummy__
var _ SimpleCallingAWSSDKFromLocalServiceImplTest.Dummy__
var _ WrappedSimpleCallingAWSSDKFromLocalServiceService.Dummy__
var _ WrappedSimpleCallingAWSSDKFromLocalServiceTest.Dummy__

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
	var _0_success bool
	_ = _0_success
	_0_success = true
	_dafny.Print((_dafny.SeqOfString("SimpleCallingAWSSDKFromLocalServiceImplTest.CallKMSEncrypt: ")).SetString())
	func() {
		defer func() {
			if r := recover(); r != nil {
				var _1_haltMessage = _dafny.SeqOfString(r.(string))
				{
					_dafny.Print((_dafny.SeqOfString("FAILED\n	")).SetString())
					_dafny.Print((_1_haltMessage).SetString())
					_dafny.Print((_dafny.SeqOfString("\n")).SetString())
					_0_success = false
				}
			}
		}()
		{
			SimpleCallingAWSSDKFromLocalServiceImplTest.Companion_Default___.CallKMSEncrypt()
			{
				_dafny.Print((_dafny.SeqOfString("PASSED\n")).SetString())
			}
		}
	}()
	_dafny.Print((_dafny.SeqOfString("WrappedSimpleCallingAWSSDKFromLocalServiceTest.TestCallKMSEncrypt: ")).SetString())
	func() {
		defer func() {
			if r := recover(); r != nil {
				var _2_haltMessage = _dafny.SeqOfString(r.(string))
				{
					_dafny.Print((_dafny.SeqOfString("FAILED\n	")).SetString())
					_dafny.Print((_2_haltMessage).SetString())
					_dafny.Print((_dafny.SeqOfString("\n")).SetString())
					_0_success = false
				}
			}
		}()
		{
			WrappedSimpleCallingAWSSDKFromLocalServiceTest.Companion_Default___.TestCallKMSEncrypt()
			{
				_dafny.Print((_dafny.SeqOfString("PASSED\n")).SetString())
			}
		}
	}()
	if !(_0_success) {
		panic("<stdin>(1,0): " + (_dafny.SeqOfString("Test failures occurred: see above.\n")).String())
	}
}

// End of class Default__
func main() {
	defer _dafny.CatchHalt()
	Companion_Default___.Test____Main____(_dafny.FromMainArguments(os.Args))
}
