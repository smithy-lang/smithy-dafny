// Package WrappedSimpleCallingAWSSDKFromLocalServiceService
// Dafny module WrappedSimpleCallingAWSSDKFromLocalServiceService compiled into Go

package WrappedSimpleCallingAWSSDKFromLocalServiceService

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
	ComAmazonawsDynamodbTypes "github.com/smithy-lang/smithy-dafny/ddb/ComAmazonawsDynamodbTypes"
	Com_Amazonaws_Dynamodb "github.com/smithy-lang/smithy-dafny/ddb/Com_Amazonaws_Dynamodb"
	ComAmazonawsKmsTypes "github.com/smithy-lang/smithy-dafny/kms/ComAmazonawsKmsTypes"
	Com_Amazonaws_Kms "github.com/smithy-lang/smithy-dafny/kms/Com_Amazonaws_Kms"
)

var _ = os.Args
var _ _dafny.Dummy__
var _ _System.Dummy__
var _ Wrappers.Dummy__
var _ StandardLibrary_UInt.Dummy__
var _ StandardLibrary.Dummy__
var _ ComAmazonawsDynamodbTypes.Dummy__
var _ ComAmazonawsKmsTypes.Dummy__
var _ SimpleCallingawssdkfromlocalserviceTypes.Dummy__
var _ Com_Amazonaws_Kms.Dummy__
var _ Com_Amazonaws_Dynamodb.Dummy__
var _ SimpleCallingAWSSDKFromLocalServiceImpl.Dummy__
var _ SimpleCallingAWSSDKFromLocalService.Dummy__
var _ StandardLibraryInterop.Dummy__
var _ SimpleCallingAWSSDKFromLocalServiceImplTest.Dummy__

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
	return "WrappedSimpleCallingAWSSDKFromLocalServiceService.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) WrappedDefaultSimpleCallingAWSSDKFromLocalServiceConfig() SimpleCallingawssdkfromlocalserviceTypes.SimpleCallingAWSSDKFromLocalServiceConfig {
	return SimpleCallingawssdkfromlocalserviceTypes.Companion_SimpleCallingAWSSDKFromLocalServiceConfig_.Create_SimpleCallingAWSSDKFromLocalServiceConfig_()
}

// End of class Default__
