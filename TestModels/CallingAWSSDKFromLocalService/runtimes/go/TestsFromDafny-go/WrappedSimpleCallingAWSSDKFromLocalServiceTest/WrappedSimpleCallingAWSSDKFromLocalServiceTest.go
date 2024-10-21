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

func (_static *CompanionStruct_Default___) TestCallDDBScan() {
	var _0_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _0_valueOrError0
	var _out0 Wrappers.Result
	_ = _out0
	_out0 = WrappedSimpleCallingAWSSDKFromLocalServiceService.Companion_Default___.WrappedSimpleCallingAWSSDKFromLocalService(WrappedSimpleCallingAWSSDKFromLocalServiceService.Companion_Default___.WrappedDefaultSimpleCallingAWSSDKFromLocalServiceConfig())
	_0_valueOrError0 = _out0
	if !(!((_0_valueOrError0).IsFailure())) {
		panic("test/WrappedSimpleCallingAWSSDKFromLocalServiceTest.dfy(23,18): " + (_0_valueOrError0).String())
	}
	var _1_client SimpleCallingawssdkfromlocalserviceTypes.ISimpleCallingAWSSDKFromLocalServiceClient
	_ = _1_client
	_1_client = SimpleCallingawssdkfromlocalserviceTypes.Companion_ISimpleCallingAWSSDKFromLocalServiceClient_.CastTo_((_0_valueOrError0).Extract())
	SimpleCallingAWSSDKFromLocalServiceImplTest.Companion_Default___.TestCallDDBScan__Success(_1_client)
	Companion_Default___.TestCallDDBScan__Failure(_1_client)
}
func (_static *CompanionStruct_Default___) TestCallKMSEncrypt() {
	var _0_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _0_valueOrError0
	var _out0 Wrappers.Result
	_ = _out0
	_out0 = WrappedSimpleCallingAWSSDKFromLocalServiceService.Companion_Default___.WrappedSimpleCallingAWSSDKFromLocalService(WrappedSimpleCallingAWSSDKFromLocalServiceService.Companion_Default___.WrappedDefaultSimpleCallingAWSSDKFromLocalServiceConfig())
	_0_valueOrError0 = _out0
	if !(!((_0_valueOrError0).IsFailure())) {
		panic("test/WrappedSimpleCallingAWSSDKFromLocalServiceTest.dfy(29,18): " + (_0_valueOrError0).String())
	}
	var _1_client SimpleCallingawssdkfromlocalserviceTypes.ISimpleCallingAWSSDKFromLocalServiceClient
	_ = _1_client
	_1_client = SimpleCallingawssdkfromlocalserviceTypes.Companion_ISimpleCallingAWSSDKFromLocalServiceClient_.CastTo_((_0_valueOrError0).Extract())
	SimpleCallingAWSSDKFromLocalServiceImplTest.Companion_Default___.TestCallKMSEncrypt__Success(_1_client)
	Companion_Default___.TestCallKMSEncrypt__Failure(_1_client)
}
func (_static *CompanionStruct_Default___) TestCallKMSEncrypt__Failure(client SimpleCallingawssdkfromlocalserviceTypes.ISimpleCallingAWSSDKFromLocalServiceClient) {
	var _0_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _0_valueOrError0
	var _out0 Wrappers.Result
	_ = _out0
	_out0 = Com_Amazonaws_Kms.Companion_Default___.KMSClient()
	_0_valueOrError0 = _out0
	if !(!((_0_valueOrError0).IsFailure())) {
		panic("test/WrappedSimpleCallingAWSSDKFromLocalServiceTest.dfy(39,21): " + (_0_valueOrError0).String())
	}
	var _1_kmsClient ComAmazonawsKmsTypes.IKMSClient
	_ = _1_kmsClient
	_1_kmsClient = ComAmazonawsKmsTypes.Companion_IKMSClient_.CastTo_((_0_valueOrError0).Extract())
	var _2_input__NonExistent ComAmazonawsKmsTypes.EncryptRequest
	_ = _2_input__NonExistent
	_2_input__NonExistent = ComAmazonawsKmsTypes.Companion_EncryptRequest_.Create_EncryptRequest_(Companion_Default___.NONEXISTENT__KEY__ID(), _dafny.SeqOf(uint8(97), uint8(115), uint8(100), uint8(102)), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_None_())
	var _3_resFailure__NonExistent Wrappers.Result
	_ = _3_resFailure__NonExistent
	var _out1 Wrappers.Result
	_ = _out1
	_out1 = (client).CallKMSEncrypt(SimpleCallingawssdkfromlocalserviceTypes.Companion_CallKMSEncryptInput_.Create_CallKMSEncryptInput_(_1_kmsClient, Companion_Default___.NONEXISTENT__KEY__ID(), Companion_Default___.PLAIN__TEXT()))
	_3_resFailure__NonExistent = _out1
	if !((_3_resFailure__NonExistent).Is_Failure()) {
		panic("test/WrappedSimpleCallingAWSSDKFromLocalServiceTest.dfy(50,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	if !((((_3_resFailure__NonExistent).Dtor_error().(SimpleCallingawssdkfromlocalserviceTypes.Error)).Dtor_ComAmazonawsKms()).Is_NotFoundException()) {
		panic("test/WrappedSimpleCallingAWSSDKFromLocalServiceTest.dfy(51,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
}
func (_static *CompanionStruct_Default___) TestCallDDBScan__Failure(client SimpleCallingawssdkfromlocalserviceTypes.ISimpleCallingAWSSDKFromLocalServiceClient) {
	var _0_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _0_valueOrError0
	var _out0 Wrappers.Result
	_ = _out0
	_out0 = Com_Amazonaws_Dynamodb.Companion_Default___.DynamoDBClient()
	_0_valueOrError0 = _out0
	if !(!((_0_valueOrError0).IsFailure())) {
		panic("test/WrappedSimpleCallingAWSSDKFromLocalServiceTest.dfy(59,21): " + (_0_valueOrError0).String())
	}
	var _1_ddbClient ComAmazonawsDynamodbTypes.IDynamoDBClient
	_ = _1_ddbClient
	_1_ddbClient = ComAmazonawsDynamodbTypes.Companion_IDynamoDBClient_.CastTo_((_0_valueOrError0).Extract())
	var _2_resFailure Wrappers.Result
	_ = _2_resFailure
	var _out1 Wrappers.Result
	_ = _out1
	_out1 = (client).CallDDBScan(SimpleCallingawssdkfromlocalserviceTypes.Companion_CallDDBScanInput_.Create_CallDDBScanInput_(_1_ddbClient, Companion_Default___.TABLE__ARN__FAILURE__CASE()))
	_2_resFailure = _out1
	if !((_2_resFailure).Is_Failure()) {
		panic("test/WrappedSimpleCallingAWSSDKFromLocalServiceTest.dfy(61,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
}
func (_static *CompanionStruct_Default___) TABLE__ARN__FAILURE__CASE() _dafny.Sequence {
	return _dafny.SeqOfString("arn:aws:dynamodb:us-west-2:370957321024:table/TestTableFailure")
}
func (_static *CompanionStruct_Default___) NONEXISTENT__KEY__ID() _dafny.Sequence {
	return _dafny.SeqOfString("arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7g")
}
func (_static *CompanionStruct_Default___) PLAIN__TEXT() _dafny.Sequence {
	return _dafny.SeqOf(uint8(97), uint8(115), uint8(100), uint8(102))
}

// End of class Default__
