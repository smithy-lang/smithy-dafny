// Package TestComAmazonawsKms
// Dafny module TestComAmazonawsKms compiled into Go

package TestComAmazonawsKms

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
	return "TestComAmazonawsKms.Default__"
}
func (_this *Default__) ParentTraits_() []*_dafny.TraitID {
	return [](*_dafny.TraitID){}
}

var _ _dafny.TraitOffspring = &Default__{}

func (_static *CompanionStruct_Default___) WorkAround(literal _dafny.Sequence) _dafny.Sequence {
	return literal
}
func (_static *CompanionStruct_Default___) BasicDecryptTests() {
	var _0_CiphertextBlob _dafny.Sequence
	_ = _0_CiphertextBlob
	_0_CiphertextBlob = _dafny.SeqOf(uint8(1), uint8(1), uint8(1), uint8(0), uint8(120), uint8(64), uint8(243), uint8(140), uint8(39), uint8(94), uint8(49), uint8(9), uint8(116), uint8(22), uint8(193), uint8(7), uint8(41), uint8(81), uint8(80), uint8(87), uint8(25), uint8(100), uint8(173), uint8(163), uint8(239), uint8(28), uint8(33), uint8(233), uint8(76), uint8(139), uint8(160), uint8(189), uint8(188), uint8(157), uint8(15), uint8(180), uint8(20), uint8(0), uint8(0), uint8(0), uint8(98), uint8(48), uint8(96), uint8(6), uint8(9), uint8(42), uint8(134), uint8(72), uint8(134), uint8(247), uint8(13), uint8(1), uint8(7), uint8(6), uint8(160), uint8(83), uint8(48), uint8(81), uint8(2), uint8(1), uint8(0), uint8(48), uint8(76), uint8(6), uint8(9), uint8(42), uint8(134), uint8(72), uint8(134), uint8(247), uint8(13), uint8(1), uint8(7), uint8(1), uint8(48), uint8(30), uint8(6), uint8(9), uint8(96), uint8(134), uint8(72), uint8(1), uint8(101), uint8(3), uint8(4), uint8(1), uint8(46), uint8(48), uint8(17), uint8(4), uint8(12), uint8(196), uint8(249), uint8(60), uint8(7), uint8(21), uint8(231), uint8(87), uint8(70), uint8(216), uint8(12), uint8(31), uint8(13), uint8(2), uint8(1), uint8(16), uint8(128), uint8(31), uint8(222), uint8(119), uint8(162), uint8(112), uint8(88), uint8(153), uint8(39), uint8(197), uint8(21), uint8(182), uint8(116), uint8(176), uint8(120), uint8(174), uint8(107), uint8(82), uint8(182), uint8(223), uint8(160), uint8(201), uint8(15), uint8(29), uint8(3), uint8(254), uint8(3), uint8(208), uint8(72), uint8(171), uint8(64), uint8(207), uint8(175))
	Companion_Default___.BasicDecryptTest(ComAmazonawsKmsTypes.Companion_DecryptRequest_.Create_DecryptRequest_(Companion_Default___.WorkAround(_0_CiphertextBlob), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_Some_(Companion_Default___.KeyId()), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_None_()), _dafny.SeqOf(uint8(165), uint8(191), uint8(67), uint8(62)), Companion_Default___.KeyId())
}
func (_static *CompanionStruct_Default___) BasicGenerateTests() {
	Companion_Default___.BasicGenerateTest(ComAmazonawsKmsTypes.Companion_GenerateDataKeyRequest_.Create_GenerateDataKeyRequest_(Companion_Default___.KeyId(), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_Some_(int32(32)), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_None_()))
}
func (_static *CompanionStruct_Default___) BasicEncryptTests() {
	Companion_Default___.BasicEncryptTest(ComAmazonawsKmsTypes.Companion_EncryptRequest_.Create_EncryptRequest_(Companion_Default___.KeyId(), _dafny.SeqOf(uint8(97), uint8(115), uint8(100), uint8(102)), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_None_()))
}
func (_static *CompanionStruct_Default___) BasicDecryptTest(input ComAmazonawsKmsTypes.DecryptRequest, expectedPlaintext _dafny.Sequence, expectedKeyId _dafny.Sequence) {
	var _1_client ComAmazonawsKmsTypes.IKMSClient
	_ = _1_client
	var _2_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _2_valueOrError0
	var _out0 Wrappers.Result
	_ = _out0
	_out0 = Com_Amazonaws_Kms.Companion_Default___.KMSClient()
	_2_valueOrError0 = _out0
	if !(!((_2_valueOrError0).IsFailure())) {
		panic("test/TestComAmazonawsKms.dfy(89,18): " + (_2_valueOrError0).String())
	}
	_1_client = ComAmazonawsKmsTypes.Companion_IKMSClient_.CastTo_((_2_valueOrError0).Extract())
	var _3_ret Wrappers.Result
	_ = _3_ret
	var _out1 Wrappers.Result
	_ = _out1
	_out1 = (_1_client).Decrypt(input)
	_3_ret = _out1
	if !((_3_ret).Is_Success()) {
		panic("test/TestComAmazonawsKms.dfy(93,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	var _let_tmp_rhs0 ComAmazonawsKmsTypes.DecryptResponse = (_3_ret).Dtor_value().(ComAmazonawsKmsTypes.DecryptResponse)
	_ = _let_tmp_rhs0
	var _4_KeyId Wrappers.Option = _let_tmp_rhs0.Get_().(ComAmazonawsKmsTypes.DecryptResponse_DecryptResponse).KeyId
	_ = _4_KeyId
	var _5_Plaintext Wrappers.Option = _let_tmp_rhs0.Get_().(ComAmazonawsKmsTypes.DecryptResponse_DecryptResponse).Plaintext
	_ = _5_Plaintext
	var _6_EncryptionAlgorithm Wrappers.Option = _let_tmp_rhs0.Get_().(ComAmazonawsKmsTypes.DecryptResponse_DecryptResponse).EncryptionAlgorithm
	_ = _6_EncryptionAlgorithm
	var _7_CipherTextReceipient Wrappers.Option = _let_tmp_rhs0.Get_().(ComAmazonawsKmsTypes.DecryptResponse_DecryptResponse).CiphertextForRecipient
	_ = _7_CipherTextReceipient
	if !((_5_Plaintext).Is_Some()) {
		panic("test/TestComAmazonawsKms.dfy(97,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	if !((_4_KeyId).Is_Some()) {
		panic("test/TestComAmazonawsKms.dfy(98,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	if !(_dafny.Companion_Sequence_.Equal((_5_Plaintext).Dtor_value().(_dafny.Sequence), expectedPlaintext)) {
		panic("test/TestComAmazonawsKms.dfy(99,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	if !(_dafny.Companion_Sequence_.Equal((_4_KeyId).Dtor_value().(_dafny.Sequence), expectedKeyId)) {
		panic("test/TestComAmazonawsKms.dfy(100,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
}
func (_static *CompanionStruct_Default___) BasicGenerateTest(input ComAmazonawsKmsTypes.GenerateDataKeyRequest) {
	var _8_client ComAmazonawsKmsTypes.IKMSClient
	_ = _8_client
	var _9_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _9_valueOrError0
	var _out2 Wrappers.Result
	_ = _out2
	_out2 = Com_Amazonaws_Kms.Companion_Default___.KMSClient()
	_9_valueOrError0 = _out2
	if !(!((_9_valueOrError0).IsFailure())) {
		panic("test/TestComAmazonawsKms.dfy(108,18): " + (_9_valueOrError0).String())
	}
	_8_client = ComAmazonawsKmsTypes.Companion_IKMSClient_.CastTo_((_9_valueOrError0).Extract())
	var _10_ret Wrappers.Result
	_ = _10_ret
	var _out3 Wrappers.Result
	_ = _out3
	_out3 = (_8_client).GenerateDataKey(input)
	_10_ret = _out3
	if !((_10_ret).Is_Success()) {
		panic("test/TestComAmazonawsKms.dfy(112,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	var _let_tmp_rhs1 ComAmazonawsKmsTypes.GenerateDataKeyResponse = (_10_ret).Dtor_value().(ComAmazonawsKmsTypes.GenerateDataKeyResponse)
	_ = _let_tmp_rhs1
	var _11_CiphertextBlob Wrappers.Option = _let_tmp_rhs1.Get_().(ComAmazonawsKmsTypes.GenerateDataKeyResponse_GenerateDataKeyResponse).CiphertextBlob
	_ = _11_CiphertextBlob
	var _12_Plaintext Wrappers.Option = _let_tmp_rhs1.Get_().(ComAmazonawsKmsTypes.GenerateDataKeyResponse_GenerateDataKeyResponse).Plaintext
	_ = _12_Plaintext
	var _13_KeyId Wrappers.Option = _let_tmp_rhs1.Get_().(ComAmazonawsKmsTypes.GenerateDataKeyResponse_GenerateDataKeyResponse).KeyId
	_ = _13_KeyId
	var _14_C Wrappers.Option = _let_tmp_rhs1.Get_().(ComAmazonawsKmsTypes.GenerateDataKeyResponse_GenerateDataKeyResponse).CiphertextForRecipient
	_ = _14_C
	if !((_11_CiphertextBlob).Is_Some()) {
		panic("test/TestComAmazonawsKms.dfy(116,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	if !((_12_Plaintext).Is_Some()) {
		panic("test/TestComAmazonawsKms.dfy(117,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	if !((_13_KeyId).Is_Some()) {
		panic("test/TestComAmazonawsKms.dfy(118,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	if !((_dafny.IntOfUint32(((_12_Plaintext).Dtor_value().(_dafny.Sequence)).Cardinality())).Cmp(_dafny.IntOfInt32(((input).Dtor_NumberOfBytes()).Dtor_value().(int32))) == 0) {
		panic("test/TestComAmazonawsKms.dfy(119,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	var _15_decryptInput ComAmazonawsKmsTypes.DecryptRequest
	_ = _15_decryptInput
	_15_decryptInput = ComAmazonawsKmsTypes.Companion_DecryptRequest_.Create_DecryptRequest_((_11_CiphertextBlob).Dtor_value().(_dafny.Sequence), (input).Dtor_EncryptionContext(), (input).Dtor_GrantTokens(), Wrappers.Companion_Option_.Create_Some_((_13_KeyId).Dtor_value().(_dafny.Sequence)), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_None_())
	Companion_Default___.BasicDecryptTest(_15_decryptInput, (_12_Plaintext).Dtor_value().(_dafny.Sequence), (input).Dtor_KeyId())
}
func (_static *CompanionStruct_Default___) BasicEncryptTest(input ComAmazonawsKmsTypes.EncryptRequest) {
	var _16_client ComAmazonawsKmsTypes.IKMSClient
	_ = _16_client
	var _17_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _17_valueOrError0
	var _out4 Wrappers.Result
	_ = _out4
	_out4 = Com_Amazonaws_Kms.Companion_Default___.KMSClient()
	_17_valueOrError0 = _out4
	if !(!((_17_valueOrError0).IsFailure())) {
		panic("test/TestComAmazonawsKms.dfy(140,18): " + (_17_valueOrError0).String())
	}
	_16_client = ComAmazonawsKmsTypes.Companion_IKMSClient_.CastTo_((_17_valueOrError0).Extract())
	var _18_ret Wrappers.Result
	_ = _18_ret
	var _out5 Wrappers.Result
	_ = _out5
	_out5 = (_16_client).Encrypt(input)
	_18_ret = _out5
	if !((_18_ret).Is_Success()) {
		panic("test/TestComAmazonawsKms.dfy(144,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	var _let_tmp_rhs2 ComAmazonawsKmsTypes.EncryptResponse = (_18_ret).Dtor_value().(ComAmazonawsKmsTypes.EncryptResponse)
	_ = _let_tmp_rhs2
	var _19_CiphertextBlob Wrappers.Option = _let_tmp_rhs2.Get_().(ComAmazonawsKmsTypes.EncryptResponse_EncryptResponse).CiphertextBlob
	_ = _19_CiphertextBlob
	var _20_KeyId Wrappers.Option = _let_tmp_rhs2.Get_().(ComAmazonawsKmsTypes.EncryptResponse_EncryptResponse).KeyId
	_ = _20_KeyId
	var _21_EncryptionAlgorithm Wrappers.Option = _let_tmp_rhs2.Get_().(ComAmazonawsKmsTypes.EncryptResponse_EncryptResponse).EncryptionAlgorithm
	_ = _21_EncryptionAlgorithm
	if !((_19_CiphertextBlob).Is_Some()) {
		panic("test/TestComAmazonawsKms.dfy(148,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	if !((_20_KeyId).Is_Some()) {
		panic("test/TestComAmazonawsKms.dfy(149,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
	var _22_decryptInput ComAmazonawsKmsTypes.DecryptRequest
	_ = _22_decryptInput
	_22_decryptInput = ComAmazonawsKmsTypes.Companion_DecryptRequest_.Create_DecryptRequest_((_19_CiphertextBlob).Dtor_value().(_dafny.Sequence), (input).Dtor_EncryptionContext(), (input).Dtor_GrantTokens(), Wrappers.Companion_Option_.Create_Some_((_20_KeyId).Dtor_value().(_dafny.Sequence)), (input).Dtor_EncryptionAlgorithm(), Wrappers.Companion_Option_.Create_None_(), Wrappers.Companion_Option_.Create_None_())
	Companion_Default___.BasicDecryptTest(_22_decryptInput, (input).Dtor_Plaintext(), (input).Dtor_KeyId())
}
func (_static *CompanionStruct_Default___) RegionMatchTest() {
	var _23_client ComAmazonawsKmsTypes.IKMSClient
	_ = _23_client
	var _24_valueOrError0 Wrappers.Result = Wrappers.Result{}
	_ = _24_valueOrError0
	var _out6 Wrappers.Result
	_ = _out6
	_out6 = Com_Amazonaws_Kms.Companion_Default___.KMSClient()
	_24_valueOrError0 = _out6
	if !(!((_24_valueOrError0).IsFailure())) {
		panic("test/TestComAmazonawsKms.dfy(169,18): " + (_24_valueOrError0).String())
	}
	_23_client = ComAmazonawsKmsTypes.Companion_IKMSClient_.CastTo_((_24_valueOrError0).Extract())
	var _25_region Wrappers.Option
	_ = _25_region
	_25_region = Com_Amazonaws_Kms.Companion_Default___.RegionMatch(_23_client, Companion_Default___.TEST__REGION())
	if !(((_25_region).Is_None()) || ((_25_region).Dtor_value().(bool))) {
		panic("test/TestComAmazonawsKms.dfy(171,4): " + (_dafny.SeqOfString("expectation violation")).String())
	}
}
func (_static *CompanionStruct_Default___) KeyId() _dafny.Sequence {
	return _dafny.SeqOfString("arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f")
}
func (_static *CompanionStruct_Default___) TEST__REGION() _dafny.Sequence {
	return _dafny.SeqOfString("us-west-2")
}

// End of class Default__
