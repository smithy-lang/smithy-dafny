// Package SimpleCallingawssdkfromlocalserviceTypes
// Dafny module SimpleCallingawssdkfromlocalserviceTypes compiled into Go

package SimpleCallingawssdkfromlocalserviceTypes

import (
	os "os"

	_System "github.com/dafny-lang/DafnyRuntimeGo/System_"
	_dafny "github.com/dafny-lang/DafnyRuntimeGo/dafny"
	StandardLibrary "github.com/dafny-lang/DafnyStandardLibGo/StandardLibrary"
	StandardLibraryInterop "github.com/dafny-lang/DafnyStandardLibGo/StandardLibraryInterop"
	StandardLibrary_UInt "github.com/dafny-lang/DafnyStandardLibGo/StandardLibrary_UInt"
	Wrappers "github.com/dafny-lang/DafnyStandardLibGo/Wrappers"
	ComAmazonawsDynamodbTypes "github.com/smithy-lang/smithy-dafny/ddb/ComAmazonawsDynamodbTypes"
	ComAmazonawsKmsTypes "github.com/smithy-lang/smithy-dafny/kms/ComAmazonawsKmsTypes"
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

type Dummy__ struct{}

// Definition of datatype DafnyCallEvent
type DafnyCallEvent struct {
	Data_DafnyCallEvent_
}

func (_this DafnyCallEvent) Get_() Data_DafnyCallEvent_ {
	return _this.Data_DafnyCallEvent_
}

type Data_DafnyCallEvent_ interface {
	isDafnyCallEvent()
}

type CompanionStruct_DafnyCallEvent_ struct {
}

var Companion_DafnyCallEvent_ = CompanionStruct_DafnyCallEvent_{}

type DafnyCallEvent_DafnyCallEvent struct {
	Input  interface{}
	Output interface{}
}

func (DafnyCallEvent_DafnyCallEvent) isDafnyCallEvent() {}

func (CompanionStruct_DafnyCallEvent_) Create_DafnyCallEvent_(Input interface{}, Output interface{}) DafnyCallEvent {
	return DafnyCallEvent{DafnyCallEvent_DafnyCallEvent{Input, Output}}
}

func (_this DafnyCallEvent) Is_DafnyCallEvent() bool {
	_, ok := _this.Get_().(DafnyCallEvent_DafnyCallEvent)
	return ok
}

func (CompanionStruct_DafnyCallEvent_) Default(_default_I interface{}, _default_O interface{}) DafnyCallEvent {
	return Companion_DafnyCallEvent_.Create_DafnyCallEvent_(_default_I, _default_O)
}

func (_this DafnyCallEvent) Dtor_input() interface{} {
	return _this.Get_().(DafnyCallEvent_DafnyCallEvent).Input
}

func (_this DafnyCallEvent) Dtor_output() interface{} {
	return _this.Get_().(DafnyCallEvent_DafnyCallEvent).Output
}

func (_this DafnyCallEvent) String() string {
	switch data := _this.Get_().(type) {
	case nil:
		return "null"
	case DafnyCallEvent_DafnyCallEvent:
		{
			return "SimpleCallingawssdkfromlocalserviceTypes.DafnyCallEvent.DafnyCallEvent" + "(" + _dafny.String(data.Input) + ", " + _dafny.String(data.Output) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this DafnyCallEvent) Equals(other DafnyCallEvent) bool {
	switch data1 := _this.Get_().(type) {
	case DafnyCallEvent_DafnyCallEvent:
		{
			data2, ok := other.Get_().(DafnyCallEvent_DafnyCallEvent)
			return ok && _dafny.AreEqual(data1.Input, data2.Input) && _dafny.AreEqual(data1.Output, data2.Output)
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this DafnyCallEvent) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(DafnyCallEvent)
	return ok && _this.Equals(typed)
}

func Type_DafnyCallEvent_(Type_I_ _dafny.TypeDescriptor, Type_O_ _dafny.TypeDescriptor) _dafny.TypeDescriptor {
	return type_DafnyCallEvent_{Type_I_, Type_O_}
}

type type_DafnyCallEvent_ struct {
	Type_I_ _dafny.TypeDescriptor
	Type_O_ _dafny.TypeDescriptor
}

func (_this type_DafnyCallEvent_) Default() interface{} {
	Type_I_ := _this.Type_I_
	_ = Type_I_
	Type_O_ := _this.Type_O_
	_ = Type_O_
	return Companion_DafnyCallEvent_.Default(Type_I_.Default(), Type_O_.Default())
}

func (_this type_DafnyCallEvent_) String() string {
	return "SimpleCallingawssdkfromlocalserviceTypes.DafnyCallEvent"
}
func (_this DafnyCallEvent) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = DafnyCallEvent{}

// End of datatype DafnyCallEvent

// Definition of datatype CallDDBScanInput
type CallDDBScanInput struct {
	Data_CallDDBScanInput_
}

func (_this CallDDBScanInput) Get_() Data_CallDDBScanInput_ {
	return _this.Data_CallDDBScanInput_
}

type Data_CallDDBScanInput_ interface {
	isCallDDBScanInput()
}

type CompanionStruct_CallDDBScanInput_ struct {
}

var Companion_CallDDBScanInput_ = CompanionStruct_CallDDBScanInput_{}

type CallDDBScanInput_CallDDBScanInput struct {
	DdbClient ComAmazonawsDynamodbTypes.IDynamoDBClient
	TableArn  _dafny.Sequence
}

func (CallDDBScanInput_CallDDBScanInput) isCallDDBScanInput() {}

func (CompanionStruct_CallDDBScanInput_) Create_CallDDBScanInput_(DdbClient ComAmazonawsDynamodbTypes.IDynamoDBClient, TableArn _dafny.Sequence) CallDDBScanInput {
	return CallDDBScanInput{CallDDBScanInput_CallDDBScanInput{DdbClient, TableArn}}
}

func (_this CallDDBScanInput) Is_CallDDBScanInput() bool {
	_, ok := _this.Get_().(CallDDBScanInput_CallDDBScanInput)
	return ok
}

func (CompanionStruct_CallDDBScanInput_) Default() CallDDBScanInput {
	return Companion_CallDDBScanInput_.Create_CallDDBScanInput_((ComAmazonawsDynamodbTypes.IDynamoDBClient)(nil), _dafny.EmptySeq.SetString())
}

func (_this CallDDBScanInput) Dtor_ddbClient() ComAmazonawsDynamodbTypes.IDynamoDBClient {
	return _this.Get_().(CallDDBScanInput_CallDDBScanInput).DdbClient
}

func (_this CallDDBScanInput) Dtor_tableArn() _dafny.Sequence {
	return _this.Get_().(CallDDBScanInput_CallDDBScanInput).TableArn
}

func (_this CallDDBScanInput) String() string {
	switch data := _this.Get_().(type) {
	case nil:
		return "null"
	case CallDDBScanInput_CallDDBScanInput:
		{
			return "SimpleCallingawssdkfromlocalserviceTypes.CallDDBScanInput.CallDDBScanInput" + "(" + _dafny.String(data.DdbClient) + ", " + _dafny.String(data.TableArn) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this CallDDBScanInput) Equals(other CallDDBScanInput) bool {
	switch data1 := _this.Get_().(type) {
	case CallDDBScanInput_CallDDBScanInput:
		{
			data2, ok := other.Get_().(CallDDBScanInput_CallDDBScanInput)
			return ok && _dafny.AreEqual(data1.DdbClient, data2.DdbClient) && data1.TableArn.Equals(data2.TableArn)
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this CallDDBScanInput) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(CallDDBScanInput)
	return ok && _this.Equals(typed)
}

func Type_CallDDBScanInput_() _dafny.TypeDescriptor {
	return type_CallDDBScanInput_{}
}

type type_CallDDBScanInput_ struct {
}

func (_this type_CallDDBScanInput_) Default() interface{} {
	return Companion_CallDDBScanInput_.Default()
}

func (_this type_CallDDBScanInput_) String() string {
	return "SimpleCallingawssdkfromlocalserviceTypes.CallDDBScanInput"
}
func (_this CallDDBScanInput) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = CallDDBScanInput{}

// End of datatype CallDDBScanInput

// Definition of datatype CallDDBScanOutput
type CallDDBScanOutput struct {
	Data_CallDDBScanOutput_
}

func (_this CallDDBScanOutput) Get_() Data_CallDDBScanOutput_ {
	return _this.Data_CallDDBScanOutput_
}

type Data_CallDDBScanOutput_ interface {
	isCallDDBScanOutput()
}

type CompanionStruct_CallDDBScanOutput_ struct {
}

var Companion_CallDDBScanOutput_ = CompanionStruct_CallDDBScanOutput_{}

type CallDDBScanOutput_CallDDBScanOutput struct {
	ItemOutput int32
}

func (CallDDBScanOutput_CallDDBScanOutput) isCallDDBScanOutput() {}

func (CompanionStruct_CallDDBScanOutput_) Create_CallDDBScanOutput_(ItemOutput int32) CallDDBScanOutput {
	return CallDDBScanOutput{CallDDBScanOutput_CallDDBScanOutput{ItemOutput}}
}

func (_this CallDDBScanOutput) Is_CallDDBScanOutput() bool {
	_, ok := _this.Get_().(CallDDBScanOutput_CallDDBScanOutput)
	return ok
}

func (CompanionStruct_CallDDBScanOutput_) Default() CallDDBScanOutput {
	return Companion_CallDDBScanOutput_.Create_CallDDBScanOutput_(int32(0))
}

func (_this CallDDBScanOutput) Dtor_itemOutput() int32 {
	return _this.Get_().(CallDDBScanOutput_CallDDBScanOutput).ItemOutput
}

func (_this CallDDBScanOutput) String() string {
	switch data := _this.Get_().(type) {
	case nil:
		return "null"
	case CallDDBScanOutput_CallDDBScanOutput:
		{
			return "SimpleCallingawssdkfromlocalserviceTypes.CallDDBScanOutput.CallDDBScanOutput" + "(" + _dafny.String(data.ItemOutput) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this CallDDBScanOutput) Equals(other CallDDBScanOutput) bool {
	switch data1 := _this.Get_().(type) {
	case CallDDBScanOutput_CallDDBScanOutput:
		{
			data2, ok := other.Get_().(CallDDBScanOutput_CallDDBScanOutput)
			return ok && data1.ItemOutput == data2.ItemOutput
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this CallDDBScanOutput) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(CallDDBScanOutput)
	return ok && _this.Equals(typed)
}

func Type_CallDDBScanOutput_() _dafny.TypeDescriptor {
	return type_CallDDBScanOutput_{}
}

type type_CallDDBScanOutput_ struct {
}

func (_this type_CallDDBScanOutput_) Default() interface{} {
	return Companion_CallDDBScanOutput_.Default()
}

func (_this type_CallDDBScanOutput_) String() string {
	return "SimpleCallingawssdkfromlocalserviceTypes.CallDDBScanOutput"
}
func (_this CallDDBScanOutput) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = CallDDBScanOutput{}

// End of datatype CallDDBScanOutput

// Definition of datatype CallKMSEncryptInput
type CallKMSEncryptInput struct {
	Data_CallKMSEncryptInput_
}

func (_this CallKMSEncryptInput) Get_() Data_CallKMSEncryptInput_ {
	return _this.Data_CallKMSEncryptInput_
}

type Data_CallKMSEncryptInput_ interface {
	isCallKMSEncryptInput()
}

type CompanionStruct_CallKMSEncryptInput_ struct {
}

var Companion_CallKMSEncryptInput_ = CompanionStruct_CallKMSEncryptInput_{}

type CallKMSEncryptInput_CallKMSEncryptInput struct {
	KmsClient ComAmazonawsKmsTypes.IKMSClient
	KeyId     _dafny.Sequence
	Plaintext _dafny.Sequence
}

func (CallKMSEncryptInput_CallKMSEncryptInput) isCallKMSEncryptInput() {}

func (CompanionStruct_CallKMSEncryptInput_) Create_CallKMSEncryptInput_(KmsClient ComAmazonawsKmsTypes.IKMSClient, KeyId _dafny.Sequence, Plaintext _dafny.Sequence) CallKMSEncryptInput {
	return CallKMSEncryptInput{CallKMSEncryptInput_CallKMSEncryptInput{KmsClient, KeyId, Plaintext}}
}

func (_this CallKMSEncryptInput) Is_CallKMSEncryptInput() bool {
	_, ok := _this.Get_().(CallKMSEncryptInput_CallKMSEncryptInput)
	return ok
}

func (CompanionStruct_CallKMSEncryptInput_) Default() CallKMSEncryptInput {
	return Companion_CallKMSEncryptInput_.Create_CallKMSEncryptInput_((ComAmazonawsKmsTypes.IKMSClient)(nil), _dafny.EmptySeq.SetString(), _dafny.EmptySeq)
}

func (_this CallKMSEncryptInput) Dtor_kmsClient() ComAmazonawsKmsTypes.IKMSClient {
	return _this.Get_().(CallKMSEncryptInput_CallKMSEncryptInput).KmsClient
}

func (_this CallKMSEncryptInput) Dtor_keyId() _dafny.Sequence {
	return _this.Get_().(CallKMSEncryptInput_CallKMSEncryptInput).KeyId
}

func (_this CallKMSEncryptInput) Dtor_plaintext() _dafny.Sequence {
	return _this.Get_().(CallKMSEncryptInput_CallKMSEncryptInput).Plaintext
}

func (_this CallKMSEncryptInput) String() string {
	switch data := _this.Get_().(type) {
	case nil:
		return "null"
	case CallKMSEncryptInput_CallKMSEncryptInput:
		{
			return "SimpleCallingawssdkfromlocalserviceTypes.CallKMSEncryptInput.CallKMSEncryptInput" + "(" + _dafny.String(data.KmsClient) + ", " + _dafny.String(data.KeyId) + ", " + _dafny.String(data.Plaintext) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this CallKMSEncryptInput) Equals(other CallKMSEncryptInput) bool {
	switch data1 := _this.Get_().(type) {
	case CallKMSEncryptInput_CallKMSEncryptInput:
		{
			data2, ok := other.Get_().(CallKMSEncryptInput_CallKMSEncryptInput)
			return ok && _dafny.AreEqual(data1.KmsClient, data2.KmsClient) && data1.KeyId.Equals(data2.KeyId) && data1.Plaintext.Equals(data2.Plaintext)
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this CallKMSEncryptInput) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(CallKMSEncryptInput)
	return ok && _this.Equals(typed)
}

func Type_CallKMSEncryptInput_() _dafny.TypeDescriptor {
	return type_CallKMSEncryptInput_{}
}

type type_CallKMSEncryptInput_ struct {
}

func (_this type_CallKMSEncryptInput_) Default() interface{} {
	return Companion_CallKMSEncryptInput_.Default()
}

func (_this type_CallKMSEncryptInput_) String() string {
	return "SimpleCallingawssdkfromlocalserviceTypes.CallKMSEncryptInput"
}
func (_this CallKMSEncryptInput) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = CallKMSEncryptInput{}

// End of datatype CallKMSEncryptInput

// Definition of datatype CallKMSEncryptOutput
type CallKMSEncryptOutput struct {
	Data_CallKMSEncryptOutput_
}

func (_this CallKMSEncryptOutput) Get_() Data_CallKMSEncryptOutput_ {
	return _this.Data_CallKMSEncryptOutput_
}

type Data_CallKMSEncryptOutput_ interface {
	isCallKMSEncryptOutput()
}

type CompanionStruct_CallKMSEncryptOutput_ struct {
}

var Companion_CallKMSEncryptOutput_ = CompanionStruct_CallKMSEncryptOutput_{}

type CallKMSEncryptOutput_CallKMSEncryptOutput struct {
	EncryptOutput _dafny.Sequence
}

func (CallKMSEncryptOutput_CallKMSEncryptOutput) isCallKMSEncryptOutput() {}

func (CompanionStruct_CallKMSEncryptOutput_) Create_CallKMSEncryptOutput_(EncryptOutput _dafny.Sequence) CallKMSEncryptOutput {
	return CallKMSEncryptOutput{CallKMSEncryptOutput_CallKMSEncryptOutput{EncryptOutput}}
}

func (_this CallKMSEncryptOutput) Is_CallKMSEncryptOutput() bool {
	_, ok := _this.Get_().(CallKMSEncryptOutput_CallKMSEncryptOutput)
	return ok
}

func (CompanionStruct_CallKMSEncryptOutput_) Default() CallKMSEncryptOutput {
	return Companion_CallKMSEncryptOutput_.Create_CallKMSEncryptOutput_(_dafny.EmptySeq.SetString())
}

func (_this CallKMSEncryptOutput) Dtor_encryptOutput() _dafny.Sequence {
	return _this.Get_().(CallKMSEncryptOutput_CallKMSEncryptOutput).EncryptOutput
}

func (_this CallKMSEncryptOutput) String() string {
	switch data := _this.Get_().(type) {
	case nil:
		return "null"
	case CallKMSEncryptOutput_CallKMSEncryptOutput:
		{
			return "SimpleCallingawssdkfromlocalserviceTypes.CallKMSEncryptOutput.CallKMSEncryptOutput" + "(" + _dafny.String(data.EncryptOutput) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this CallKMSEncryptOutput) Equals(other CallKMSEncryptOutput) bool {
	switch data1 := _this.Get_().(type) {
	case CallKMSEncryptOutput_CallKMSEncryptOutput:
		{
			data2, ok := other.Get_().(CallKMSEncryptOutput_CallKMSEncryptOutput)
			return ok && data1.EncryptOutput.Equals(data2.EncryptOutput)
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this CallKMSEncryptOutput) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(CallKMSEncryptOutput)
	return ok && _this.Equals(typed)
}

func Type_CallKMSEncryptOutput_() _dafny.TypeDescriptor {
	return type_CallKMSEncryptOutput_{}
}

type type_CallKMSEncryptOutput_ struct {
}

func (_this type_CallKMSEncryptOutput_) Default() interface{} {
	return Companion_CallKMSEncryptOutput_.Default()
}

func (_this type_CallKMSEncryptOutput_) String() string {
	return "SimpleCallingawssdkfromlocalserviceTypes.CallKMSEncryptOutput"
}
func (_this CallKMSEncryptOutput) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = CallKMSEncryptOutput{}

// End of datatype CallKMSEncryptOutput

// Definition of class ISimpleCallingAWSSDKFromLocalServiceClientCallHistory
type ISimpleCallingAWSSDKFromLocalServiceClientCallHistory struct {
	dummy byte
}

func New_ISimpleCallingAWSSDKFromLocalServiceClientCallHistory_() *ISimpleCallingAWSSDKFromLocalServiceClientCallHistory {
	_this := ISimpleCallingAWSSDKFromLocalServiceClientCallHistory{}

	return &_this
}

type CompanionStruct_ISimpleCallingAWSSDKFromLocalServiceClientCallHistory_ struct {
}

var Companion_ISimpleCallingAWSSDKFromLocalServiceClientCallHistory_ = CompanionStruct_ISimpleCallingAWSSDKFromLocalServiceClientCallHistory_{}

func (_this *ISimpleCallingAWSSDKFromLocalServiceClientCallHistory) Equals(other *ISimpleCallingAWSSDKFromLocalServiceClientCallHistory) bool {
	return _this == other
}

func (_this *ISimpleCallingAWSSDKFromLocalServiceClientCallHistory) EqualsGeneric(x interface{}) bool {
	other, ok := x.(*ISimpleCallingAWSSDKFromLocalServiceClientCallHistory)
	return ok && _this.Equals(other)
}

func (*ISimpleCallingAWSSDKFromLocalServiceClientCallHistory) String() string {
	return "SimpleCallingawssdkfromlocalserviceTypes.ISimpleCallingAWSSDKFromLocalServiceClientCallHistory"
}

func Type_ISimpleCallingAWSSDKFromLocalServiceClientCallHistory_() _dafny.TypeDescriptor {
	return type_ISimpleCallingAWSSDKFromLocalServiceClientCallHistory_{}
}

type type_ISimpleCallingAWSSDKFromLocalServiceClientCallHistory_ struct {
}

func (_this type_ISimpleCallingAWSSDKFromLocalServiceClientCallHistory_) Default() interface{} {
	return (*ISimpleCallingAWSSDKFromLocalServiceClientCallHistory)(nil)
}

func (_this type_ISimpleCallingAWSSDKFromLocalServiceClientCallHistory_) String() string {
	return "SimpleCallingawssdkfromlocalserviceTypes.ISimpleCallingAWSSDKFromLocalServiceClientCallHistory"
}
func (_this *ISimpleCallingAWSSDKFromLocalServiceClientCallHistory) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &ISimpleCallingAWSSDKFromLocalServiceClientCallHistory{}

// End of class ISimpleCallingAWSSDKFromLocalServiceClientCallHistory

// Definition of trait ISimpleCallingAWSSDKFromLocalServiceClient
type ISimpleCallingAWSSDKFromLocalServiceClient interface {
	String() string
	CallDDBScan(input CallDDBScanInput) Wrappers.Result
	CallKMSEncrypt(input CallKMSEncryptInput) Wrappers.Result
}
type CompanionStruct_ISimpleCallingAWSSDKFromLocalServiceClient_ struct {
	TraitID_ *_dafny.TraitID
}

var Companion_ISimpleCallingAWSSDKFromLocalServiceClient_ = CompanionStruct_ISimpleCallingAWSSDKFromLocalServiceClient_{
	TraitID_: &_dafny.TraitID{},
}

func (CompanionStruct_ISimpleCallingAWSSDKFromLocalServiceClient_) CastTo_(x interface{}) ISimpleCallingAWSSDKFromLocalServiceClient {
	var t ISimpleCallingAWSSDKFromLocalServiceClient
	t, _ = x.(ISimpleCallingAWSSDKFromLocalServiceClient)
	return t
}

// End of trait ISimpleCallingAWSSDKFromLocalServiceClient

// Definition of datatype SimpleCallingAWSSDKFromLocalServiceConfig
type SimpleCallingAWSSDKFromLocalServiceConfig struct {
	Data_SimpleCallingAWSSDKFromLocalServiceConfig_
}

func (_this SimpleCallingAWSSDKFromLocalServiceConfig) Get_() Data_SimpleCallingAWSSDKFromLocalServiceConfig_ {
	return _this.Data_SimpleCallingAWSSDKFromLocalServiceConfig_
}

type Data_SimpleCallingAWSSDKFromLocalServiceConfig_ interface {
	isSimpleCallingAWSSDKFromLocalServiceConfig()
}

type CompanionStruct_SimpleCallingAWSSDKFromLocalServiceConfig_ struct {
}

var Companion_SimpleCallingAWSSDKFromLocalServiceConfig_ = CompanionStruct_SimpleCallingAWSSDKFromLocalServiceConfig_{}

type SimpleCallingAWSSDKFromLocalServiceConfig_SimpleCallingAWSSDKFromLocalServiceConfig struct {
}

func (SimpleCallingAWSSDKFromLocalServiceConfig_SimpleCallingAWSSDKFromLocalServiceConfig) isSimpleCallingAWSSDKFromLocalServiceConfig() {
}

func (CompanionStruct_SimpleCallingAWSSDKFromLocalServiceConfig_) Create_SimpleCallingAWSSDKFromLocalServiceConfig_() SimpleCallingAWSSDKFromLocalServiceConfig {
	return SimpleCallingAWSSDKFromLocalServiceConfig{SimpleCallingAWSSDKFromLocalServiceConfig_SimpleCallingAWSSDKFromLocalServiceConfig{}}
}

func (_this SimpleCallingAWSSDKFromLocalServiceConfig) Is_SimpleCallingAWSSDKFromLocalServiceConfig() bool {
	_, ok := _this.Get_().(SimpleCallingAWSSDKFromLocalServiceConfig_SimpleCallingAWSSDKFromLocalServiceConfig)
	return ok
}

func (CompanionStruct_SimpleCallingAWSSDKFromLocalServiceConfig_) Default() SimpleCallingAWSSDKFromLocalServiceConfig {
	return Companion_SimpleCallingAWSSDKFromLocalServiceConfig_.Create_SimpleCallingAWSSDKFromLocalServiceConfig_()
}

func (_ CompanionStruct_SimpleCallingAWSSDKFromLocalServiceConfig_) AllSingletonConstructors() _dafny.Iterator {
	i := -1
	return func() (interface{}, bool) {
		i++
		switch i {
		case 0:
			return Companion_SimpleCallingAWSSDKFromLocalServiceConfig_.Create_SimpleCallingAWSSDKFromLocalServiceConfig_(), true
		default:
			return SimpleCallingAWSSDKFromLocalServiceConfig{}, false
		}
	}
}

func (_this SimpleCallingAWSSDKFromLocalServiceConfig) String() string {
	switch _this.Get_().(type) {
	case nil:
		return "null"
	case SimpleCallingAWSSDKFromLocalServiceConfig_SimpleCallingAWSSDKFromLocalServiceConfig:
		{
			return "SimpleCallingawssdkfromlocalserviceTypes.SimpleCallingAWSSDKFromLocalServiceConfig.SimpleCallingAWSSDKFromLocalServiceConfig"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this SimpleCallingAWSSDKFromLocalServiceConfig) Equals(other SimpleCallingAWSSDKFromLocalServiceConfig) bool {
	switch _this.Get_().(type) {
	case SimpleCallingAWSSDKFromLocalServiceConfig_SimpleCallingAWSSDKFromLocalServiceConfig:
		{
			_, ok := other.Get_().(SimpleCallingAWSSDKFromLocalServiceConfig_SimpleCallingAWSSDKFromLocalServiceConfig)
			return ok
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this SimpleCallingAWSSDKFromLocalServiceConfig) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(SimpleCallingAWSSDKFromLocalServiceConfig)
	return ok && _this.Equals(typed)
}

func Type_SimpleCallingAWSSDKFromLocalServiceConfig_() _dafny.TypeDescriptor {
	return type_SimpleCallingAWSSDKFromLocalServiceConfig_{}
}

type type_SimpleCallingAWSSDKFromLocalServiceConfig_ struct {
}

func (_this type_SimpleCallingAWSSDKFromLocalServiceConfig_) Default() interface{} {
	return Companion_SimpleCallingAWSSDKFromLocalServiceConfig_.Default()
}

func (_this type_SimpleCallingAWSSDKFromLocalServiceConfig_) String() string {
	return "SimpleCallingawssdkfromlocalserviceTypes.SimpleCallingAWSSDKFromLocalServiceConfig"
}
func (_this SimpleCallingAWSSDKFromLocalServiceConfig) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = SimpleCallingAWSSDKFromLocalServiceConfig{}

// End of datatype SimpleCallingAWSSDKFromLocalServiceConfig

// Definition of datatype Error
type Error struct {
	Data_Error_
}

func (_this Error) Get_() Data_Error_ {
	return _this.Data_Error_
}

type Data_Error_ interface {
	isError()
}

type CompanionStruct_Error_ struct {
}

var Companion_Error_ = CompanionStruct_Error_{}

type Error_SimpleCallingAWSSDKFromLocalServiceException struct {
	Message _dafny.Sequence
}

func (Error_SimpleCallingAWSSDKFromLocalServiceException) isError() {}

func (CompanionStruct_Error_) Create_SimpleCallingAWSSDKFromLocalServiceException_(Message _dafny.Sequence) Error {
	return Error{Error_SimpleCallingAWSSDKFromLocalServiceException{Message}}
}

func (_this Error) Is_SimpleCallingAWSSDKFromLocalServiceException() bool {
	_, ok := _this.Get_().(Error_SimpleCallingAWSSDKFromLocalServiceException)
	return ok
}

type Error_ComAmazonawsDynamodb struct {
	ComAmazonawsDynamodb ComAmazonawsDynamodbTypes.Error
}

func (Error_ComAmazonawsDynamodb) isError() {}

func (CompanionStruct_Error_) Create_ComAmazonawsDynamodb_(ComAmazonawsDynamodb ComAmazonawsDynamodbTypes.Error) Error {
	return Error{Error_ComAmazonawsDynamodb{ComAmazonawsDynamodb}}
}

func (_this Error) Is_ComAmazonawsDynamodb() bool {
	_, ok := _this.Get_().(Error_ComAmazonawsDynamodb)
	return ok
}

type Error_ComAmazonawsKms struct {
	ComAmazonawsKms ComAmazonawsKmsTypes.Error
}

func (Error_ComAmazonawsKms) isError() {}

func (CompanionStruct_Error_) Create_ComAmazonawsKms_(ComAmazonawsKms ComAmazonawsKmsTypes.Error) Error {
	return Error{Error_ComAmazonawsKms{ComAmazonawsKms}}
}

func (_this Error) Is_ComAmazonawsKms() bool {
	_, ok := _this.Get_().(Error_ComAmazonawsKms)
	return ok
}

type Error_CollectionOfErrors struct {
	List    _dafny.Sequence
	Message _dafny.Sequence
}

func (Error_CollectionOfErrors) isError() {}

func (CompanionStruct_Error_) Create_CollectionOfErrors_(List _dafny.Sequence, Message _dafny.Sequence) Error {
	return Error{Error_CollectionOfErrors{List, Message}}
}

func (_this Error) Is_CollectionOfErrors() bool {
	_, ok := _this.Get_().(Error_CollectionOfErrors)
	return ok
}

type Error_Opaque struct {
	Obj interface{}
}

func (Error_Opaque) isError() {}

func (CompanionStruct_Error_) Create_Opaque_(Obj interface{}) Error {
	return Error{Error_Opaque{Obj}}
}

func (_this Error) Is_Opaque() bool {
	_, ok := _this.Get_().(Error_Opaque)
	return ok
}

func (CompanionStruct_Error_) Default() Error {
	return Companion_Error_.Create_SimpleCallingAWSSDKFromLocalServiceException_(_dafny.EmptySeq.SetString())
}

func (_this Error) Dtor_message() _dafny.Sequence {
	switch data := _this.Get_().(type) {
	case Error_SimpleCallingAWSSDKFromLocalServiceException:
		return data.Message
	default:
		return data.(Error_CollectionOfErrors).Message
	}
}

func (_this Error) Dtor_ComAmazonawsDynamodb() ComAmazonawsDynamodbTypes.Error {
	return _this.Get_().(Error_ComAmazonawsDynamodb).ComAmazonawsDynamodb
}

func (_this Error) Dtor_ComAmazonawsKms() ComAmazonawsKmsTypes.Error {
	return _this.Get_().(Error_ComAmazonawsKms).ComAmazonawsKms
}

func (_this Error) Dtor_list() _dafny.Sequence {
	return _this.Get_().(Error_CollectionOfErrors).List
}

func (_this Error) Dtor_obj() interface{} {
	return _this.Get_().(Error_Opaque).Obj
}

func (_this Error) String() string {
	switch data := _this.Get_().(type) {
	case nil:
		return "null"
	case Error_SimpleCallingAWSSDKFromLocalServiceException:
		{
			return "SimpleCallingawssdkfromlocalserviceTypes.Error.SimpleCallingAWSSDKFromLocalServiceException" + "(" + _dafny.String(data.Message) + ")"
		}
	case Error_ComAmazonawsDynamodb:
		{
			return "SimpleCallingawssdkfromlocalserviceTypes.Error.ComAmazonawsDynamodb" + "(" + _dafny.String(data.ComAmazonawsDynamodb) + ")"
		}
	case Error_ComAmazonawsKms:
		{
			return "SimpleCallingawssdkfromlocalserviceTypes.Error.ComAmazonawsKms" + "(" + _dafny.String(data.ComAmazonawsKms) + ")"
		}
	case Error_CollectionOfErrors:
		{
			return "SimpleCallingawssdkfromlocalserviceTypes.Error.CollectionOfErrors" + "(" + _dafny.String(data.List) + ", " + _dafny.String(data.Message) + ")"
		}
	case Error_Opaque:
		{
			return "SimpleCallingawssdkfromlocalserviceTypes.Error.Opaque" + "(" + _dafny.String(data.Obj) + ")"
		}
	default:
		{
			return "<unexpected>"
		}
	}
}

func (_this Error) Equals(other Error) bool {
	switch data1 := _this.Get_().(type) {
	case Error_SimpleCallingAWSSDKFromLocalServiceException:
		{
			data2, ok := other.Get_().(Error_SimpleCallingAWSSDKFromLocalServiceException)
			return ok && data1.Message.Equals(data2.Message)
		}
	case Error_ComAmazonawsDynamodb:
		{
			data2, ok := other.Get_().(Error_ComAmazonawsDynamodb)
			return ok && data1.ComAmazonawsDynamodb.Equals(data2.ComAmazonawsDynamodb)
		}
	case Error_ComAmazonawsKms:
		{
			data2, ok := other.Get_().(Error_ComAmazonawsKms)
			return ok && data1.ComAmazonawsKms.Equals(data2.ComAmazonawsKms)
		}
	case Error_CollectionOfErrors:
		{
			data2, ok := other.Get_().(Error_CollectionOfErrors)
			return ok && data1.List.Equals(data2.List) && data1.Message.Equals(data2.Message)
		}
	case Error_Opaque:
		{
			data2, ok := other.Get_().(Error_Opaque)
			return ok && _dafny.AreEqual(data1.Obj, data2.Obj)
		}
	default:
		{
			return false // unexpected
		}
	}
}

func (_this Error) EqualsGeneric(other interface{}) bool {
	typed, ok := other.(Error)
	return ok && _this.Equals(typed)
}

func Type_Error_() _dafny.TypeDescriptor {
	return type_Error_{}
}

type type_Error_ struct {
}

func (_this type_Error_) Default() interface{} {
	return Companion_Error_.Default()
}

func (_this type_Error_) String() string {
	return "SimpleCallingawssdkfromlocalserviceTypes.Error"
}
func (_this Error) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = Error{}

// End of datatype Error

// Definition of class OpaqueError
type OpaqueError struct {
}

func New_OpaqueError_() *OpaqueError {
	_this := OpaqueError{}

	return &_this
}

type CompanionStruct_OpaqueError_ struct {
}

var Companion_OpaqueError_ = CompanionStruct_OpaqueError_{}

func (*OpaqueError) String() string {
	return "SimpleCallingawssdkfromlocalserviceTypes.OpaqueError"
}

// End of class OpaqueError

func Type_OpaqueError_() _dafny.TypeDescriptor {
	return type_OpaqueError_{}
}

type type_OpaqueError_ struct {
}

func (_this type_OpaqueError_) Default() interface{} {
	return Companion_Error_.Default()
}

func (_this type_OpaqueError_) String() string {
	return "SimpleCallingawssdkfromlocalserviceTypes.OpaqueError"
}
func (_this *CompanionStruct_OpaqueError_) Is_(__source Error) bool {
	var _0_e Error = (__source)
	_ = _0_e
	return (_0_e).Is_Opaque()
}
