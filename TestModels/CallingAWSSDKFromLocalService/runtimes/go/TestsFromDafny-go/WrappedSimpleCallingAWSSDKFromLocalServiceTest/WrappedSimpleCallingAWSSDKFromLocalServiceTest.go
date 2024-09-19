// Package WrappedSimpleCallingAWSSDKFromLocalServiceTest
// Dafny module WrappedSimpleCallingAWSSDKFromLocalServiceTest compiled into Go

package WrappedSimpleCallingAWSSDKFromLocalServiceTest

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
	return "WrappedSimpleCallingAWSSDKFromLocalServiceTest.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) TestCallKMSEncrypt() {
	var _0_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _0_valueOrError0
	var _out0 Wrappers.Result
	_ = _out0
	_out0 = WrappedSimpleCallingAWSSDKFromLocalServiceService.Companion_Default___.WrappedSimpleCallingAWSSDKFromLocalService(WrappedSimpleCallingAWSSDKFromLocalServiceService.Companion_Default___.WrappedDefaultSimpleCallingAWSSDKFromLocalServiceConfig())
	_0_valueOrError0 = _out0
	if !(!((_0_valueOrError0).IsFailure())) {
		panic("test/WrappedSimpleCallingAWSSDKFromLocalServiceTest.dfy(18,18): " + (_0_valueOrError0).String())
	}
	var _1_client SimpleCallingawssdkfromlocalserviceTypes.ISimpleCallingAWSSDKFromLocalServiceClient
	_ = _1_client
	_1_client = SimpleCallingawssdkfromlocalserviceTypes.Companion_ISimpleCallingAWSSDKFromLocalServiceClient_.CastTo_((_0_valueOrError0).Extract())
	SimpleCallingAWSSDKFromLocalServiceImplTest.Companion_Default___.TestCallKMSEncrypt__Success(_1_client)
	SimpleCallingAWSSDKFromLocalServiceImplTest.Companion_Default___.TestCallKMSEncrypt__Failure(_1_client)
}

// End of class Default__
