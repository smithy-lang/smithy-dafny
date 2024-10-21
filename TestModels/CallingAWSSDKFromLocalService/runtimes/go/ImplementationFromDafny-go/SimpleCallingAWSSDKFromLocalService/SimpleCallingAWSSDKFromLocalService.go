// Package SimpleCallingAWSSDKFromLocalService
// Dafny module SimpleCallingAWSSDKFromLocalService compiled into Go

package SimpleCallingAWSSDKFromLocalService

import (
	os "os"

	_System "github.com/dafny-lang/DafnyRuntimeGo/System_"
	_dafny "github.com/dafny-lang/DafnyRuntimeGo/dafny"
	StandardLibrary "github.com/dafny-lang/DafnyStandardLibGo/StandardLibrary"
	StandardLibraryInterop "github.com/dafny-lang/DafnyStandardLibGo/StandardLibraryInterop"
	StandardLibrary_UInt "github.com/dafny-lang/DafnyStandardLibGo/StandardLibrary_UInt"
	Wrappers "github.com/dafny-lang/DafnyStandardLibGo/Wrappers"
	SimpleCallingAWSSDKFromLocalServiceImpl "github.com/smithy-lang/smithy-dafny/TestModels/CallingAWSSDKFromLocalService/SimpleCallingAWSSDKFromLocalServiceImpl"
	SimpleCallingawssdkfromlocalserviceTypes "github.com/smithy-lang/smithy-dafny/TestModels/CallingAWSSDKFromLocalService/SimpleCallingawssdkfromlocalserviceTypes"
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
var _ StandardLibraryInterop.Dummy__
var _ SimpleCallingawssdkfromlocalserviceTypes.Dummy__
var _ Com_Amazonaws_Kms.Dummy__
var _ Com_Amazonaws_Dynamodb.Dummy__
var _ SimpleCallingAWSSDKFromLocalServiceImpl.Dummy__

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
	return "SimpleCallingAWSSDKFromLocalService.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) DefaultSimpleCallingAWSSDKFromLocalServiceConfig() SimpleCallingawssdkfromlocalserviceTypes.SimpleCallingAWSSDKFromLocalServiceConfig {
	return SimpleCallingawssdkfromlocalserviceTypes.Companion_SimpleCallingAWSSDKFromLocalServiceConfig_.Create_SimpleCallingAWSSDKFromLocalServiceConfig_()
}
func (_static *CompanionStruct_Default___) SimpleCallingAWSSDKFromLocalService(config SimpleCallingawssdkfromlocalserviceTypes.SimpleCallingAWSSDKFromLocalServiceConfig) Wrappers.Result {
	var res Wrappers.Result = Wrappers.Result{}
	_ = res
	var _0_client *SimpleCallingAWSSDKFromLocalServiceClient
	_ = _0_client
	var _nw0 *SimpleCallingAWSSDKFromLocalServiceClient = New_SimpleCallingAWSSDKFromLocalServiceClient_()
	_ = _nw0
	_nw0.Ctor__(SimpleCallingAWSSDKFromLocalServiceImpl.Companion_Config_.Create_Config_())
	_0_client = _nw0
	res = Wrappers.Companion_Result_.Create_Success_(_0_client)
	return res
	return res
}
func (_static *CompanionStruct_Default___) CreateSuccessOfClient(client SimpleCallingawssdkfromlocalserviceTypes.ISimpleCallingAWSSDKFromLocalServiceClient) Wrappers.Result {
	return Wrappers.Companion_Result_.Create_Success_(client)
}
func (_static *CompanionStruct_Default___) CreateFailureOfError(error_ SimpleCallingawssdkfromlocalserviceTypes.Error) Wrappers.Result {
	return Wrappers.Companion_Result_.Create_Failure_(error_)
}

// End of class Default__

// Definition of class SimpleCallingAWSSDKFromLocalServiceClient
type SimpleCallingAWSSDKFromLocalServiceClient struct {
	_config SimpleCallingAWSSDKFromLocalServiceImpl.Config
}

func New_SimpleCallingAWSSDKFromLocalServiceClient_() *SimpleCallingAWSSDKFromLocalServiceClient {
	_this := SimpleCallingAWSSDKFromLocalServiceClient{}

	_this._config = SimpleCallingAWSSDKFromLocalServiceImpl.Companion_Config_.Default()
	return &_this
}

type CompanionStruct_SimpleCallingAWSSDKFromLocalServiceClient_ struct {
}

var Companion_SimpleCallingAWSSDKFromLocalServiceClient_ = CompanionStruct_SimpleCallingAWSSDKFromLocalServiceClient_{}

func (_this *SimpleCallingAWSSDKFromLocalServiceClient) Equals(other *SimpleCallingAWSSDKFromLocalServiceClient) bool {
	return _this == other
}

func (_this *SimpleCallingAWSSDKFromLocalServiceClient) EqualsGeneric(x interface{}) bool {
	other, ok := x.(*SimpleCallingAWSSDKFromLocalServiceClient)
	return ok && _this.Equals(other)
}

func (*SimpleCallingAWSSDKFromLocalServiceClient) String() string {
	return "SimpleCallingAWSSDKFromLocalService.SimpleCallingAWSSDKFromLocalServiceClient"
}

func Type_SimpleCallingAWSSDKFromLocalServiceClient_() _dafny.TypeDescriptor {
	return type_SimpleCallingAWSSDKFromLocalServiceClient_{}
}

type type_SimpleCallingAWSSDKFromLocalServiceClient_ struct {
}

func (_this type_SimpleCallingAWSSDKFromLocalServiceClient_) Default() interface{} {
	return (*SimpleCallingAWSSDKFromLocalServiceClient)(nil)
}

func (_this type_SimpleCallingAWSSDKFromLocalServiceClient_) String() string {
	return "SimpleCallingAWSSDKFromLocalService.SimpleCallingAWSSDKFromLocalServiceClient"
}
func (_this *SimpleCallingAWSSDKFromLocalServiceClient) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){SimpleCallingawssdkfromlocalserviceTypes.Companion_ISimpleCallingAWSSDKFromLocalServiceClient_.TraitID_}
}

var _ SimpleCallingawssdkfromlocalserviceTypes.ISimpleCallingAWSSDKFromLocalServiceClient = &SimpleCallingAWSSDKFromLocalServiceClient{}
var _ _dafny.TraitOffspring = &SimpleCallingAWSSDKFromLocalServiceClient{}

func (_this *SimpleCallingAWSSDKFromLocalServiceClient) Ctor__(config SimpleCallingAWSSDKFromLocalServiceImpl.Config) {
	{
		(_this)._config = config
	}
}
func (_this *SimpleCallingAWSSDKFromLocalServiceClient) CallDDBScan(input SimpleCallingawssdkfromlocalserviceTypes.CallDDBScanInput) Wrappers.Result {
	{
		var output Wrappers.Result = Wrappers.Companion_Result_.Default(SimpleCallingawssdkfromlocalserviceTypes.Companion_CallDDBScanOutput_.Default())
		_ = output
		var _out0 Wrappers.Result
		_ = _out0
		_out0 = SimpleCallingAWSSDKFromLocalServiceImpl.Companion_Default___.CallDDBScan((_this).Config(), input)
		output = _out0
		return output
	}
}
func (_this *SimpleCallingAWSSDKFromLocalServiceClient) CallKMSEncrypt(input SimpleCallingawssdkfromlocalserviceTypes.CallKMSEncryptInput) Wrappers.Result {
	{
		var output Wrappers.Result = Wrappers.Result{}
		_ = output
		var _out0 Wrappers.Result
		_ = _out0
		_out0 = SimpleCallingAWSSDKFromLocalServiceImpl.Companion_Default___.CallKMSEncrypt((_this).Config(), input)
		output = _out0
		return output
	}
}
func (_this *SimpleCallingAWSSDKFromLocalServiceClient) Config() SimpleCallingAWSSDKFromLocalServiceImpl.Config {
	{
		return _this._config
	}
}

// End of class SimpleCallingAWSSDKFromLocalServiceClient
