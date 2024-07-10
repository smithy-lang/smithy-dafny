#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]

pub mod r#_TestComAmazonawsKms_Compile {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn workAround(literal: &::dafny_runtime::Sequence<u8>) -> super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType{
            literal.clone()
        }
        pub fn BasicDecryptTests() -> () {
            let mut CiphertextBlob: ::dafny_runtime::Sequence<u8> = ::dafny_runtime::seq![
                1, 1, 1, 0, 120, 64, 243, 140, 39, 94, 49, 9, 116, 22, 193, 7, 41, 81, 80, 87, 25,
                100, 173, 163, 239, 28, 33, 233, 76, 139, 160, 189, 188, 157, 15, 180, 20, 0, 0, 0,
                98, 48, 96, 6, 9, 42, 134, 72, 134, 247, 13, 1, 7, 6, 160, 83, 48, 81, 2, 1, 0, 48,
                76, 6, 9, 42, 134, 72, 134, 247, 13, 1, 7, 1, 48, 30, 6, 9, 96, 134, 72, 1, 101, 3,
                4, 1, 46, 48, 17, 4, 12, 196, 249, 60, 7, 21, 231, 87, 70, 216, 12, 31, 13, 2, 1,
                16, 128, 31, 222, 119, 162, 112, 88, 153, 39, 197, 21, 182, 116, 176, 120, 174,
                107, 82, 182, 223, 160, 201, 15, 29, 3, 254, 3, 208, 72, 171, 64, 207, 175
            ];
            super::r#_TestComAmazonawsKms_Compile::_default::BasicDecryptTest(&::std::rc::Rc::new(super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DecryptRequest::DecryptRequest {
            CiphertextBlob: super::r#_TestComAmazonawsKms_Compile::_default::workAround(&CiphertextBlob),
            EncryptionContext: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>::None {}),
            GrantTokens: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GrantTokenList>::None {}),
            KeyId: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: super::r#_TestComAmazonawsKms_Compile::_default::keyId()
                }),
            EncryptionAlgorithm: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>::None {}),
            Recipient: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::RecipientInfo>>::None {}),
            DryRun: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::None {})
          }), &::dafny_runtime::seq![165, 191, 67, 62], &super::r#_TestComAmazonawsKms_Compile::_default::keyId());
            return ();
        }
        pub fn BasicGenerateTests() -> () {
            super::r#_TestComAmazonawsKms_Compile::_default::BasicGenerateTest(&::std::rc::Rc::new(super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GenerateDataKeyRequest::GenerateDataKeyRequest {
            KeyId: super::r#_TestComAmazonawsKms_Compile::_default::keyId(),
            EncryptionContext: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>::None {}),
            NumberOfBytes: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::NumberOfBytesType>::Some {
                  value: 32
                }),
            KeySpec: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DataKeySpec>>::None {}),
            GrantTokens: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GrantTokenList>::None {}),
            Recipient: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::RecipientInfo>>::None {}),
            DryRun: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::None {})
          }));
            return ();
        }
        pub fn BasicEncryptTests() -> () {
            super::r#_TestComAmazonawsKms_Compile::_default::BasicEncryptTest(&::std::rc::Rc::new(super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptRequest::EncryptRequest {
            KeyId: super::r#_TestComAmazonawsKms_Compile::_default::keyId(),
            Plaintext: ::dafny_runtime::seq![97, 115, 100, 102],
            EncryptionContext: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>::None {}),
            GrantTokens: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GrantTokenList>::None {}),
            EncryptionAlgorithm: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>::None {}),
            DryRun: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::None {})
          }));
            return ();
        }
        pub fn BasicDecryptTest(
            input: &::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DecryptRequest>,
            expectedPlaintext: &super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::PlaintextType,
            expectedKeyId: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        ) -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>>>::new();
            _out0 = ::dafny_runtime::MaybePlacebo::from(super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny::_default::KMSClient());
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out0.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient> = valueOrError0.read().Extract();
            let mut ret = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DecryptResponse>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out1 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DecryptResponse>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>>>::new();
            _out1 = ::dafny_runtime::MaybePlacebo::from(super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient::Decrypt(::dafny_runtime::md!(client.clone()), input));
            ret = ::dafny_runtime::MaybePlacebo::from(_out1.read());
            if !matches!(
                (&ret.read()).as_ref(),
                super::r#_Wrappers_Compile::Result::Success { .. }
            ) {
                panic!("Halt")
            };
            let mut r#__let_tmp_rhs0: ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DecryptResponse> = ret.read().value().clone();
            let mut KeyId: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            > = r#__let_tmp_rhs0.KeyId().clone();
            let mut Plaintext: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::PlaintextType>> = r#__let_tmp_rhs0.Plaintext().clone();
            let mut EncryptionAlgorithm: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>> = r#__let_tmp_rhs0.EncryptionAlgorithm().clone();
            let mut CiphertextBlob: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType>> = r#__let_tmp_rhs0.CiphertextForRecipient().clone();
            if !matches!(
                (&Plaintext).as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !matches!(
                (&KeyId).as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !(Plaintext.value().clone() == expectedPlaintext.clone()) {
                panic!("Halt")
            };
            if !(KeyId.value().clone() == expectedKeyId.clone()) {
                panic!("Halt")
            };
            return ();
        }
        pub fn BasicGenerateTest(
            input: &::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GenerateDataKeyRequest>,
        ) -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out2 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>>>::new();
            _out2 = ::dafny_runtime::MaybePlacebo::from(super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny::_default::KMSClient());
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out2.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient> = valueOrError0.read().Extract();
            let mut ret = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GenerateDataKeyResponse>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out3 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GenerateDataKeyResponse>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>>>::new();
            _out3 = ::dafny_runtime::MaybePlacebo::from(super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient::GenerateDataKey(::dafny_runtime::md!(client.clone()), input));
            ret = ::dafny_runtime::MaybePlacebo::from(_out3.read());
            if !matches!(
                (&ret.read()).as_ref(),
                super::r#_Wrappers_Compile::Result::Success { .. }
            ) {
                panic!("Halt")
            };
            let mut r#__let_tmp_rhs1: ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GenerateDataKeyResponse> = ret.read().value().clone();
            let mut CiphertextBlob: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType>> = r#__let_tmp_rhs1.CiphertextBlob().clone();
            let mut Plaintext: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::PlaintextType>> = r#__let_tmp_rhs1.Plaintext().clone();
            let mut KeyId: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            > = r#__let_tmp_rhs1.KeyId().clone();
            let mut CiphertextForRecipient: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType>> = r#__let_tmp_rhs1.CiphertextForRecipient().clone();
            if !matches!(
                (&CiphertextBlob).as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !matches!(
                (&Plaintext).as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !matches!(
                (&KeyId).as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !(Plaintext.value().cardinality()
                == Into::<::dafny_runtime::DafnyInt>::into(input.NumberOfBytes().value().clone()))
            {
                panic!("Halt")
            };
            let mut decryptInput: ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DecryptRequest> = ::std::rc::Rc::new(super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DecryptRequest::DecryptRequest {
            CiphertextBlob: CiphertextBlob.value().clone(),
            EncryptionContext: input.EncryptionContext().clone(),
            GrantTokens: input.GrantTokens().clone(),
            KeyId: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: KeyId.value().clone()
                }),
            EncryptionAlgorithm: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>::None {}),
            Recipient: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::RecipientInfo>>::None {}),
            DryRun: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::None {})
          });
            super::r#_TestComAmazonawsKms_Compile::_default::BasicDecryptTest(
                &decryptInput,
                Plaintext.value(),
                input.KeyId(),
            );
            return ();
        }
        pub fn BasicEncryptTest(
            input: &::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptRequest>,
        ) -> () {
            let mut valueOrError0 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out4 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>>>::new();
            _out4 = ::dafny_runtime::MaybePlacebo::from(super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny::_default::KMSClient());
            valueOrError0 = ::dafny_runtime::MaybePlacebo::from(_out4.read());
            if !(!valueOrError0.read().IsFailure()) {
                panic!("Halt")
            };
            let mut client: ::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient> = valueOrError0.read().Extract();
            let mut ret = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptResponse>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>>>::new();
            let mut _out5 = ::dafny_runtime::MaybePlacebo::<::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptResponse>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>>>::new();
            _out5 = ::dafny_runtime::MaybePlacebo::from(super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient::Encrypt(::dafny_runtime::md!(client.clone()), input));
            ret = ::dafny_runtime::MaybePlacebo::from(_out5.read());
            if !matches!(
                (&ret.read()).as_ref(),
                super::r#_Wrappers_Compile::Result::Success { .. }
            ) {
                panic!("Halt")
            };
            let mut r#__let_tmp_rhs2: ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptResponse> = ret.read().value().clone();
            let mut CiphertextBlob: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType>> = r#__let_tmp_rhs2.CiphertextBlob().clone();
            let mut KeyId: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            > = r#__let_tmp_rhs2.KeyId().clone();
            let mut EncryptionAlgorithm: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>> = r#__let_tmp_rhs2.EncryptionAlgorithm().clone();
            if !matches!(
                (&CiphertextBlob).as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            if !matches!(
                (&KeyId).as_ref(),
                super::r#_Wrappers_Compile::Option::Some { .. }
            ) {
                panic!("Halt")
            };
            let mut decryptInput: ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DecryptRequest> = ::std::rc::Rc::new(super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DecryptRequest::DecryptRequest {
            CiphertextBlob: CiphertextBlob.value().clone(),
            EncryptionContext: input.EncryptionContext().clone(),
            GrantTokens: input.GrantTokens().clone(),
            KeyId: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>::Some {
                  value: KeyId.value().clone()
                }),
            EncryptionAlgorithm: input.EncryptionAlgorithm().clone(),
            Recipient: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::RecipientInfo>>::None {}),
            DryRun: ::std::rc::Rc::new(super::r#_Wrappers_Compile::Option::<bool>::None {})
          });
            super::r#_TestComAmazonawsKms_Compile::_default::BasicDecryptTest(
                &decryptInput,
                input.Plaintext(),
                input.KeyId(),
            );
            return ();
        }
        pub fn keyId() -> ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            ::dafny_runtime::string_utf16_of(
                "arn:aws:kms:us-west-2:658956600833:key/b3537ef1-d8dc-4780-9f5a-55776cbb2f7f",
            )
        }
        pub fn TEST_REGION() -> ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            ::dafny_runtime::string_utf16_of("us-west-2")
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_TestComAmazonawsKms_Compile::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
pub mod _module {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn _Test__Main_() -> () {
            let mut success: bool = true;
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"TestComAmazonawsKms.BasicDecryptTests: "#
                ))
            );
            super::r#_TestComAmazonawsKms_Compile::_default::BasicDecryptTests();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"TestComAmazonawsKms.BasicGenerateTests: "#
                ))
            );
            super::r#_TestComAmazonawsKms_Compile::_default::BasicGenerateTests();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"TestComAmazonawsKms.BasicEncryptTests: "#
                ))
            );
            super::r#_TestComAmazonawsKms_Compile::_default::BasicEncryptTests();
            print!(
                "{}",
                ::dafny_runtime::DafnyPrintWrapper(&::dafny_runtime::string_utf16_of(
                    r#"PASSED
"#
                ))
            );
            if !success {
                panic!("Halt")
            };
            return ();
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any> for super::_module::_default {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }
}
fn main() {
    _module::_default::_Test__Main_();
}
