// Package SimpleCallingAWSSDKFromLocalServiceImplTest
// Dafny module SimpleCallingAWSSDKFromLocalServiceImplTest compiled into Go

package SimpleCallingAWSSDKFromLocalServiceImplTest

import (
	"fmt"
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
	SimpleCallingAWSSDKFromLocalService "github.com/smithy-lang/smithy-dafny/TestModels/CallingAWSSDKFromLocalService/SimpleCallingAWSSDKFromLocalService"
	SimpleCallingAWSSDKFromLocalServiceImpl "github.com/smithy-lang/smithy-dafny/TestModels/CallingAWSSDKFromLocalService/SimpleCallingAWSSDKFromLocalServiceImpl"
	SimpleCallingawssdkfromlocalserviceTypes "github.com/smithy-lang/smithy-dafny/TestModels/CallingAWSSDKFromLocalService/SimpleCallingawssdkfromlocalserviceTypes"
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
var _ Com_Amazonaws.Dummy__
var _ Com.Dummy__
var _ SimpleCallingAWSSDKFromLocalServiceImpl.Dummy__
var _ SimpleCallingAWSSDKFromLocalService.Dummy__
var _ StandardLibraryInterop.Dummy__

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
	return "SimpleCallingAWSSDKFromLocalServiceImplTest.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) CallKMSEncrypt() {
	var _0_client *SimpleCallingAWSSDKFromLocalService.SimpleCallingAWSSDKFromLocalServiceClient
	_ = _0_client
	var _1_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _1_valueOrError0
	var _out0 Wrappers.Result
	_ = _out0
	_out0 = SimpleCallingAWSSDKFromLocalService.Companion_Default___.SimpleCallingAWSSDKFromLocalService(SimpleCallingAWSSDKFromLocalService.Companion_Default___.DefaultSimpleCallingAWSSDKFromLocalServiceConfig())
	_1_valueOrError0 = _out0
	if !(!((_1_valueOrError0).IsFailure())) {
		panic("test/SimpleCallingAWSSDKFromLocalServiceImplTest.dfy(80,18): " + (_1_valueOrError0).String())
	}
	_0_client = (_1_valueOrError0).Extract().(*SimpleCallingAWSSDKFromLocalService.SimpleCallingAWSSDKFromLocalServiceClient)
	Companion_Default___.TestCallKMSEncrypt__Success(_0_client)
	Companion_Default___.TestCallKMSEncrypt__Failure(_0_client)
}
func (_static *CompanionStruct_Default___) TestCallKMSEncrypt__Success(client SimpleCallingawssdkfromlocalserviceTypes.ISimpleCallingAWSSDKFromLocalServiceClient) {
	var _2_kmsClient ComAmazonawsKmsTypes.IKMSClient
	_ = _2_kmsClient
	var _3_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _3_valueOrError0
	var _out1 Wrappers.Result
	_ = _out1
	_out1 = Com_Amazonaws_Kms.Companion_Default___.KMSClient()
	_3_valueOrError0 = _out1
	if !(!((_3_valueOrError0).IsFailure())) {
		panic("test/SimpleCallingAWSSDKFromLocalServiceImplTest.dfy(90,21): " + (_3_valueOrError0).String())
	}
	_2_kmsClient = ComAmazonawsKmsTypes.Companion_IKMSClient_.CastTo_((_3_valueOrError0).Extract())
	var _4_resSuccess Wrappers.Result
	_ = _4_resSuccess
	var _out2 Wrappers.Result
	_ = _out2
	_out2 = (client).CallKMSEncrypt(SimpleCallingawssdkfromlocalserviceTypes.Companion_CallKMSEncryptInput_.Create_CallKMSEncryptInput_(_2_kmsClient, Companion_Default___.KEY__ID__SUCCESS__CASE(), Companion_Default___.PLAIN__TEXT()))
	_4_resSuccess = _out2
	if !((_4_resSuccess).Is_Success()) {
		panic("test/SimpleCallingAWSSDKFromLocalServiceImplTest.dfy(92,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
}

// recover function to handle panic
func handlePanic() {

	// detect if panic occurs or not
	a := recover()

	if a != nil {
		fmt.Println("RECOVER", a)
	}

}
func (_static *CompanionStruct_Default___) TestCallKMSEncrypt__Failure(client SimpleCallingawssdkfromlocalserviceTypes.ISimpleCallingAWSSDKFromLocalServiceClient) {
	var _5_kmsClient ComAmazonawsKmsTypes.IKMSClient
	_ = _5_kmsClient
	var _6_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _6_valueOrError0
	var _out3 Wrappers.Result
	_ = _out3
	_out3 = Com_Amazonaws_Kms.Companion_Default___.KMSClient()
	_6_valueOrError0 = _out3
	if !(!((_6_valueOrError0).IsFailure())) {
		panic("test/SimpleCallingAWSSDKFromLocalServiceImplTest.dfy(100,21): " + (_6_valueOrError0).String())
	}
	_5_kmsClient = ComAmazonawsKmsTypes.Companion_IKMSClient_.CastTo_((_6_valueOrError0).Extract())
	var _7_input__InvalidKey ComAmazonawsKmsTypes.EncryptRequest
	_ = _7_input__InvalidKey
	_7_input__InvalidKey = ComAmazonawsKmsTypes.Companion_EncryptRequest_.Create_EncryptRequest_(Companion_Default___.INVALID__KEY__ID(), _dafny.SeqOf(uint8(97), uint8(115), uint8(100), uint8(102)), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_None_())
	var _8_resFailure__InvalidKey Wrappers.Result
	_ = _8_resFailure__InvalidKey
	var _out4 Wrappers.Result
	_ = _out4
	defer handlePanic()
	// fmt.Println((client).CallKMSEncrypt(SimpleCallingawssdkfromlocalserviceTypes.Companion_CallKMSEncryptInput_.Create_CallKMSEncryptInput_(_5_kmsClient, Companion_Default___.INVALID__KEY__ID(), Companion_Default___.PLAIN__TEXT())))
	_out4 = (client).CallKMSEncrypt(SimpleCallingawssdkfromlocalserviceTypes.Companion_CallKMSEncryptInput_.Create_CallKMSEncryptInput_(_5_kmsClient, Companion_Default___.INVALID__KEY__ID(), Companion_Default___.PLAIN__TEXT()))
	_8_resFailure__InvalidKey = _out4
	if !((_8_resFailure__InvalidKey).Is_Failure()) {
		panic("test/SimpleCallingAWSSDKFromLocalServiceImplTest.dfy(111,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	var _9_input__NonExistent ComAmazonawsKmsTypes.EncryptRequest
	_ = _9_input__NonExistent
	_9_input__NonExistent = ComAmazonawsKmsTypes.Companion_EncryptRequest_.Create_EncryptRequest_(Companion_Default___.NONEXISTENT__KEY__ID(), _dafny.SeqOf(uint8(97), uint8(115), uint8(100), uint8(102)), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_None_())
	var _10_resFailure__NonExistent Wrappers.Result
	_ = _10_resFailure__NonExistent
	var _out5 Wrappers.Result
	_ = _out5
	_out5 = (client).CallKMSEncrypt(SimpleCallingawssdkfromlocalserviceTypes.Companion_CallKMSEncryptInput_.Create_CallKMSEncryptInput_(_5_kmsClient, Companion_Default___.NONEXISTENT__KEY__ID(), Companion_Default___.PLAIN__TEXT()))
	_10_resFailure__NonExistent = _out5
	if !((_10_resFailure__NonExistent).Is_Failure()) {
		panic("test/SimpleCallingAWSSDKFromLocalServiceImplTest.dfy(122,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
}
func (_static *CompanionStruct_Default___) KEY__ID__SUCCESS__CASE() _dafny.Sequence {
	return _dafny.SeqOfString("arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f")
}
func (_static *CompanionStruct_Default___) PLAIN__TEXT() _dafny.Sequence {
	return _dafny.SeqOf(uint8(97), uint8(115), uint8(100), uint8(102))
}
func (_static *CompanionStruct_Default___) INVALID__KEY__ID() _dafny.Sequence {
	return _dafny.SeqOfString("arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-invalidkeyid")
}
func (_static *CompanionStruct_Default___) NONEXISTENT__KEY__ID() _dafny.Sequence {
	return _dafny.SeqOfString("arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7g")
}
func (_static *CompanionStruct_Default___) TABLE__NAME__SUCCESS__CASE() _dafny.Sequence {
	return _dafny.SeqOfString("TestTable")
}
func (_static *CompanionStruct_Default___) NONEXISTENT__TABLE__NAME() _dafny.Sequence {
	return _dafny.SeqOfString("NONEXISTENT_Table")
}

// End of class Default__
