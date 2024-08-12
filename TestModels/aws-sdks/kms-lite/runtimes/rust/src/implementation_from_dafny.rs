#![allow(warnings, unconditional_panic)]
#![allow(nonstandard_style)]
pub mod r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn IsValid_AttestationDocumentType(x: &::dafny_runtime::Sequence<u8>) -> bool {
            ::dafny_runtime::int!(1) <= x.cardinality()
                && x.cardinality() <= ::dafny_runtime::int!(b"262144")
        }
        pub fn IsValid_CiphertextType(x: &::dafny_runtime::Sequence<u8>) -> bool {
            ::dafny_runtime::int!(1) <= x.cardinality()
                && x.cardinality() <= ::dafny_runtime::int!(6144)
        }
        pub fn IsValid_GrantTokenList(
            x: &::dafny_runtime::Sequence<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        ) -> bool {
            ::dafny_runtime::int!(0) <= x.cardinality()
                && x.cardinality() <= ::dafny_runtime::int!(10)
        }
        pub fn IsValid_GrantTokenType(
            x: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        ) -> bool {
            ::dafny_runtime::int!(1) <= x.cardinality()
                && x.cardinality() <= ::dafny_runtime::int!(8192)
        }
        pub fn IsValid_KeyIdType(
            x: &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        ) -> bool {
            ::dafny_runtime::int!(1) <= x.cardinality()
                && x.cardinality() <= ::dafny_runtime::int!(2048)
        }
        pub fn IsValid_NumberOfBytesType(x: i32) -> bool {
            1 <= x && x <= 1024
        }
        pub fn IsValid_PlaintextType(x: &::dafny_runtime::Sequence<u8>) -> bool {
            ::dafny_runtime::int!(1) <= x.cardinality()
                && x.cardinality() <= ::dafny_runtime::int!(4096)
        }
        pub fn IsValid_PublicKeyType(x: &::dafny_runtime::Sequence<u8>) -> bool {
            ::dafny_runtime::int!(1) <= x.cardinality()
                && x.cardinality() <= ::dafny_runtime::int!(8192)
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }

    #[derive(PartialEq, Clone)]
    pub enum DafnyCallEvent<I: ::dafny_runtime::DafnyType, O: ::dafny_runtime::DafnyType> {
        DafnyCallEvent { input: I, output: O },
        _PhantomVariant(::std::marker::PhantomData<I>, ::std::marker::PhantomData<O>),
    }

    impl<I: ::dafny_runtime::DafnyType, O: ::dafny_runtime::DafnyType> DafnyCallEvent<I, O> {
        pub fn input(&self) -> &I {
            match self {
                DafnyCallEvent::DafnyCallEvent { input, output } => input,
                DafnyCallEvent::_PhantomVariant(..) => panic!(),
            }
        }
        pub fn output(&self) -> &O {
            match self {
                DafnyCallEvent::DafnyCallEvent { input, output } => output,
                DafnyCallEvent::_PhantomVariant(..) => panic!(),
            }
        }
    }

    impl<I: ::dafny_runtime::DafnyType, O: ::dafny_runtime::DafnyType> ::std::fmt::Debug
        for DafnyCallEvent<I, O>
    {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl<I: ::dafny_runtime::DafnyType, O: ::dafny_runtime::DafnyType> ::dafny_runtime::DafnyPrint
        for DafnyCallEvent<I, O>
    {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                DafnyCallEvent::DafnyCallEvent { input, output } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.DafnyCallEvent.DafnyCallEvent(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(input, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(output, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                DafnyCallEvent::_PhantomVariant(..) => {
                    panic!()
                }
            }
        }
    }

    impl<I: ::dafny_runtime::DafnyType + Eq, O: ::dafny_runtime::DafnyType + Eq> Eq
        for DafnyCallEvent<I, O>
    {
    }

    impl<
            I: ::dafny_runtime::DafnyType + ::std::hash::Hash,
            O: ::dafny_runtime::DafnyType + ::std::hash::Hash,
        > ::std::hash::Hash for DafnyCallEvent<I, O>
    {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                DafnyCallEvent::DafnyCallEvent { input, output } => {
                    input.hash(_state);
                    output.hash(_state)
                }
                DafnyCallEvent::_PhantomVariant(..) => {
                    panic!()
                }
            }
        }
    }

    impl<
            I: ::dafny_runtime::DafnyType + ::std::default::Default,
            O: ::dafny_runtime::DafnyType + ::std::default::Default,
        > ::std::default::Default for DafnyCallEvent<I, O>
    {
        fn default() -> DafnyCallEvent<I, O> {
            DafnyCallEvent::DafnyCallEvent {
                input: ::std::default::Default::default(),
                output: ::std::default::Default::default(),
            }
        }
    }

    impl<I: ::dafny_runtime::DafnyType, O: ::dafny_runtime::DafnyType>
        ::std::convert::AsRef<DafnyCallEvent<I, O>> for &DafnyCallEvent<I, O>
    {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub type AttestationDocumentType = ::dafny_runtime::Sequence<u8>;

    pub type CiphertextType = ::dafny_runtime::Sequence<u8>;

    #[derive(PartialEq, Clone)]
    pub enum CustomerMasterKeySpec {
        RSA_2048 {},
        RSA_3072 {},
        RSA_4096 {},
        ECC_NIST_P256 {},
        ECC_NIST_P384 {},
        ECC_NIST_P521 {},
        ECC_SECG_P256K1 {},
        SYMMETRIC_DEFAULT {},
        HMAC_224 {},
        HMAC_256 {},
        HMAC_384 {},
        HMAC_512 {},
        SM2 {},
    }

    impl CustomerMasterKeySpec {}

    impl ::std::fmt::Debug for CustomerMasterKeySpec {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for CustomerMasterKeySpec {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                CustomerMasterKeySpec::RSA_2048 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.RSA__2048")?;
                    Ok(())
                }
                CustomerMasterKeySpec::RSA_3072 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.RSA__3072")?;
                    Ok(())
                }
                CustomerMasterKeySpec::RSA_4096 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.RSA__4096")?;
                    Ok(())
                }
                CustomerMasterKeySpec::ECC_NIST_P256 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.ECC__NIST__P256")?;
                    Ok(())
                }
                CustomerMasterKeySpec::ECC_NIST_P384 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.ECC__NIST__P384")?;
                    Ok(())
                }
                CustomerMasterKeySpec::ECC_NIST_P521 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.ECC__NIST__P521")?;
                    Ok(())
                }
                CustomerMasterKeySpec::ECC_SECG_P256K1 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.ECC__SECG__P256K1")?;
                    Ok(())
                }
                CustomerMasterKeySpec::SYMMETRIC_DEFAULT {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.SYMMETRIC__DEFAULT")?;
                    Ok(())
                }
                CustomerMasterKeySpec::HMAC_224 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.HMAC__224")?;
                    Ok(())
                }
                CustomerMasterKeySpec::HMAC_256 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.HMAC__256")?;
                    Ok(())
                }
                CustomerMasterKeySpec::HMAC_384 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.HMAC__384")?;
                    Ok(())
                }
                CustomerMasterKeySpec::HMAC_512 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.HMAC__512")?;
                    Ok(())
                }
                CustomerMasterKeySpec::SM2 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.CustomerMasterKeySpec.SM2")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for CustomerMasterKeySpec {}

    impl ::std::hash::Hash for CustomerMasterKeySpec {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                CustomerMasterKeySpec::RSA_2048 {} => {}
                CustomerMasterKeySpec::RSA_3072 {} => {}
                CustomerMasterKeySpec::RSA_4096 {} => {}
                CustomerMasterKeySpec::ECC_NIST_P256 {} => {}
                CustomerMasterKeySpec::ECC_NIST_P384 {} => {}
                CustomerMasterKeySpec::ECC_NIST_P521 {} => {}
                CustomerMasterKeySpec::ECC_SECG_P256K1 {} => {}
                CustomerMasterKeySpec::SYMMETRIC_DEFAULT {} => {}
                CustomerMasterKeySpec::HMAC_224 {} => {}
                CustomerMasterKeySpec::HMAC_256 {} => {}
                CustomerMasterKeySpec::HMAC_384 {} => {}
                CustomerMasterKeySpec::HMAC_512 {} => {}
                CustomerMasterKeySpec::SM2 {} => {}
            }
        }
    }

    impl ::std::default::Default for CustomerMasterKeySpec {
        fn default() -> CustomerMasterKeySpec {
            CustomerMasterKeySpec::RSA_2048 {}
        }
    }

    impl ::std::convert::AsRef<CustomerMasterKeySpec> for &CustomerMasterKeySpec {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum DataKeySpec {
        AES_256 {},
        AES_128 {},
    }

    impl DataKeySpec {}

    impl ::std::fmt::Debug for DataKeySpec {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for DataKeySpec {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                DataKeySpec::AES_256 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.DataKeySpec.AES__256")?;
                    Ok(())
                }
                DataKeySpec::AES_128 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.DataKeySpec.AES__128")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for DataKeySpec {}

    impl ::std::hash::Hash for DataKeySpec {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                DataKeySpec::AES_256 {} => {}
                DataKeySpec::AES_128 {} => {}
            }
        }
    }

    impl ::std::default::Default for DataKeySpec {
        fn default() -> DataKeySpec {
            DataKeySpec::AES_256 {}
        }
    }

    impl ::std::convert::AsRef<DataKeySpec> for &DataKeySpec {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum DecryptRequest {
        DecryptRequest {
      CiphertextBlob: super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType,
      EncryptionContext: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>>,
      GrantTokens: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GrantTokenList>>,
      KeyId: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
      EncryptionAlgorithm: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>>,
      Recipient: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::RecipientInfo>>>,
      DryRun: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>>
    }
  }

    impl DecryptRequest {
        pub fn CiphertextBlob(&self) -> &super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType{
            match self {
                DecryptRequest::DecryptRequest {
                    CiphertextBlob,
                    EncryptionContext,
                    GrantTokens,
                    KeyId,
                    EncryptionAlgorithm,
                    Recipient,
                    DryRun,
                } => CiphertextBlob,
            }
        }
        pub fn EncryptionContext(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Map<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        > {
            match self {
                DecryptRequest::DecryptRequest {
                    CiphertextBlob,
                    EncryptionContext,
                    GrantTokens,
                    KeyId,
                    EncryptionAlgorithm,
                    Recipient,
                    DryRun,
                } => EncryptionContext,
            }
        }
        pub fn GrantTokens(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GrantTokenList>>{
            match self {
                DecryptRequest::DecryptRequest {
                    CiphertextBlob,
                    EncryptionContext,
                    GrantTokens,
                    KeyId,
                    EncryptionAlgorithm,
                    Recipient,
                    DryRun,
                } => GrantTokens,
            }
        }
        pub fn KeyId(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
                DecryptRequest::DecryptRequest {
                    CiphertextBlob,
                    EncryptionContext,
                    GrantTokens,
                    KeyId,
                    EncryptionAlgorithm,
                    Recipient,
                    DryRun,
                } => KeyId,
            }
        }
        pub fn EncryptionAlgorithm(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>>{
            match self {
                DecryptRequest::DecryptRequest {
                    CiphertextBlob,
                    EncryptionContext,
                    GrantTokens,
                    KeyId,
                    EncryptionAlgorithm,
                    Recipient,
                    DryRun,
                } => EncryptionAlgorithm,
            }
        }
        pub fn Recipient(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::RecipientInfo>>>{
            match self {
                DecryptRequest::DecryptRequest {
                    CiphertextBlob,
                    EncryptionContext,
                    GrantTokens,
                    KeyId,
                    EncryptionAlgorithm,
                    Recipient,
                    DryRun,
                } => Recipient,
            }
        }
        pub fn DryRun(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>> {
            match self {
                DecryptRequest::DecryptRequest {
                    CiphertextBlob,
                    EncryptionContext,
                    GrantTokens,
                    KeyId,
                    EncryptionAlgorithm,
                    Recipient,
                    DryRun,
                } => DryRun,
            }
        }
    }

    impl ::std::fmt::Debug for DecryptRequest {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for DecryptRequest {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                DecryptRequest::DecryptRequest {
                    CiphertextBlob,
                    EncryptionContext,
                    GrantTokens,
                    KeyId,
                    EncryptionAlgorithm,
                    Recipient,
                    DryRun,
                } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.DecryptRequest.DecryptRequest(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(CiphertextBlob, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(EncryptionContext, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(GrantTokens, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(KeyId, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(EncryptionAlgorithm, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(Recipient, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(DryRun, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for DecryptRequest {}

    impl ::std::hash::Hash for DecryptRequest {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                DecryptRequest::DecryptRequest {
                    CiphertextBlob,
                    EncryptionContext,
                    GrantTokens,
                    KeyId,
                    EncryptionAlgorithm,
                    Recipient,
                    DryRun,
                } => {
                    CiphertextBlob.hash(_state);
                    EncryptionContext.hash(_state);
                    GrantTokens.hash(_state);
                    KeyId.hash(_state);
                    EncryptionAlgorithm.hash(_state);
                    Recipient.hash(_state);
                    DryRun.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for DecryptRequest {
        fn default() -> DecryptRequest {
            DecryptRequest::DecryptRequest {
                CiphertextBlob: ::std::default::Default::default(),
                EncryptionContext: ::std::default::Default::default(),
                GrantTokens: ::std::default::Default::default(),
                KeyId: ::std::default::Default::default(),
                EncryptionAlgorithm: ::std::default::Default::default(),
                Recipient: ::std::default::Default::default(),
                DryRun: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<DecryptRequest> for &DecryptRequest {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum DecryptResponse {
        DecryptResponse {
      KeyId: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
      Plaintext: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::PlaintextType>>,
      EncryptionAlgorithm: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>>,
      CiphertextForRecipient: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType>>
    }
  }

    impl DecryptResponse {
        pub fn KeyId(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
                DecryptResponse::DecryptResponse {
                    KeyId,
                    Plaintext,
                    EncryptionAlgorithm,
                    CiphertextForRecipient,
                } => KeyId,
            }
        }
        pub fn Plaintext(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::PlaintextType>>{
            match self {
                DecryptResponse::DecryptResponse {
                    KeyId,
                    Plaintext,
                    EncryptionAlgorithm,
                    CiphertextForRecipient,
                } => Plaintext,
            }
        }
        pub fn EncryptionAlgorithm(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>>{
            match self {
                DecryptResponse::DecryptResponse {
                    KeyId,
                    Plaintext,
                    EncryptionAlgorithm,
                    CiphertextForRecipient,
                } => EncryptionAlgorithm,
            }
        }
        pub fn CiphertextForRecipient(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType>>{
            match self {
                DecryptResponse::DecryptResponse {
                    KeyId,
                    Plaintext,
                    EncryptionAlgorithm,
                    CiphertextForRecipient,
                } => CiphertextForRecipient,
            }
        }
    }

    impl ::std::fmt::Debug for DecryptResponse {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for DecryptResponse {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                DecryptResponse::DecryptResponse {
                    KeyId,
                    Plaintext,
                    EncryptionAlgorithm,
                    CiphertextForRecipient,
                } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.DecryptResponse.DecryptResponse(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(KeyId, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(Plaintext, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(EncryptionAlgorithm, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(
                        CiphertextForRecipient,
                        _formatter,
                        false,
                    )?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for DecryptResponse {}

    impl ::std::hash::Hash for DecryptResponse {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                DecryptResponse::DecryptResponse {
                    KeyId,
                    Plaintext,
                    EncryptionAlgorithm,
                    CiphertextForRecipient,
                } => {
                    KeyId.hash(_state);
                    Plaintext.hash(_state);
                    EncryptionAlgorithm.hash(_state);
                    CiphertextForRecipient.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for DecryptResponse {
        fn default() -> DecryptResponse {
            DecryptResponse::DecryptResponse {
                KeyId: ::std::default::Default::default(),
                Plaintext: ::std::default::Default::default(),
                EncryptionAlgorithm: ::std::default::Default::default(),
                CiphertextForRecipient: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<DecryptResponse> for &DecryptResponse {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum DeriveSharedSecretRequest {
        DeriveSharedSecretRequest {
      KeyId: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
      KeyAgreementAlgorithm: ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyAgreementAlgorithmSpec>,
      PublicKey: super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::PublicKeyType,
      GrantTokens: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GrantTokenList>>,
      DryRun: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>>,
      Recipient: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::RecipientInfo>>>
    }
  }

    impl DeriveSharedSecretRequest {
        pub fn KeyId(&self) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            match self {
                DeriveSharedSecretRequest::DeriveSharedSecretRequest {
                    KeyId,
                    KeyAgreementAlgorithm,
                    PublicKey,
                    GrantTokens,
                    DryRun,
                    Recipient,
                } => KeyId,
            }
        }
        pub fn KeyAgreementAlgorithm(&self) -> &::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyAgreementAlgorithmSpec>{
            match self {
                DeriveSharedSecretRequest::DeriveSharedSecretRequest {
                    KeyId,
                    KeyAgreementAlgorithm,
                    PublicKey,
                    GrantTokens,
                    DryRun,
                    Recipient,
                } => KeyAgreementAlgorithm,
            }
        }
        pub fn PublicKey(&self) -> &super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::PublicKeyType{
            match self {
                DeriveSharedSecretRequest::DeriveSharedSecretRequest {
                    KeyId,
                    KeyAgreementAlgorithm,
                    PublicKey,
                    GrantTokens,
                    DryRun,
                    Recipient,
                } => PublicKey,
            }
        }
        pub fn GrantTokens(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GrantTokenList>>{
            match self {
                DeriveSharedSecretRequest::DeriveSharedSecretRequest {
                    KeyId,
                    KeyAgreementAlgorithm,
                    PublicKey,
                    GrantTokens,
                    DryRun,
                    Recipient,
                } => GrantTokens,
            }
        }
        pub fn DryRun(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>> {
            match self {
                DeriveSharedSecretRequest::DeriveSharedSecretRequest {
                    KeyId,
                    KeyAgreementAlgorithm,
                    PublicKey,
                    GrantTokens,
                    DryRun,
                    Recipient,
                } => DryRun,
            }
        }
        pub fn Recipient(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::RecipientInfo>>>{
            match self {
                DeriveSharedSecretRequest::DeriveSharedSecretRequest {
                    KeyId,
                    KeyAgreementAlgorithm,
                    PublicKey,
                    GrantTokens,
                    DryRun,
                    Recipient,
                } => Recipient,
            }
        }
    }

    impl ::std::fmt::Debug for DeriveSharedSecretRequest {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for DeriveSharedSecretRequest {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                DeriveSharedSecretRequest::DeriveSharedSecretRequest {
                    KeyId,
                    KeyAgreementAlgorithm,
                    PublicKey,
                    GrantTokens,
                    DryRun,
                    Recipient,
                } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.DeriveSharedSecretRequest.DeriveSharedSecretRequest(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(KeyId, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(
                        KeyAgreementAlgorithm,
                        _formatter,
                        false,
                    )?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(PublicKey, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(GrantTokens, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(DryRun, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(Recipient, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for DeriveSharedSecretRequest {}

    impl ::std::hash::Hash for DeriveSharedSecretRequest {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                DeriveSharedSecretRequest::DeriveSharedSecretRequest {
                    KeyId,
                    KeyAgreementAlgorithm,
                    PublicKey,
                    GrantTokens,
                    DryRun,
                    Recipient,
                } => {
                    KeyId.hash(_state);
                    KeyAgreementAlgorithm.hash(_state);
                    PublicKey.hash(_state);
                    GrantTokens.hash(_state);
                    DryRun.hash(_state);
                    Recipient.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for DeriveSharedSecretRequest {
        fn default() -> DeriveSharedSecretRequest {
            DeriveSharedSecretRequest::DeriveSharedSecretRequest {
                KeyId: ::std::default::Default::default(),
                KeyAgreementAlgorithm: ::std::default::Default::default(),
                PublicKey: ::std::default::Default::default(),
                GrantTokens: ::std::default::Default::default(),
                DryRun: ::std::default::Default::default(),
                Recipient: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<DeriveSharedSecretRequest> for &DeriveSharedSecretRequest {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum DeriveSharedSecretResponse {
        DeriveSharedSecretResponse {
      KeyId: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
      SharedSecret: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::PlaintextType>>,
      CiphertextForRecipient: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType>>,
      KeyAgreementAlgorithm: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyAgreementAlgorithmSpec>>>,
      KeyOrigin: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::OriginType>>>
    }
  }

    impl DeriveSharedSecretResponse {
        pub fn KeyId(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
                DeriveSharedSecretResponse::DeriveSharedSecretResponse {
                    KeyId,
                    SharedSecret,
                    CiphertextForRecipient,
                    KeyAgreementAlgorithm,
                    KeyOrigin,
                } => KeyId,
            }
        }
        pub fn SharedSecret(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::PlaintextType>>{
            match self {
                DeriveSharedSecretResponse::DeriveSharedSecretResponse {
                    KeyId,
                    SharedSecret,
                    CiphertextForRecipient,
                    KeyAgreementAlgorithm,
                    KeyOrigin,
                } => SharedSecret,
            }
        }
        pub fn CiphertextForRecipient(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType>>{
            match self {
                DeriveSharedSecretResponse::DeriveSharedSecretResponse {
                    KeyId,
                    SharedSecret,
                    CiphertextForRecipient,
                    KeyAgreementAlgorithm,
                    KeyOrigin,
                } => CiphertextForRecipient,
            }
        }
        pub fn KeyAgreementAlgorithm(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyAgreementAlgorithmSpec>>>{
            match self {
                DeriveSharedSecretResponse::DeriveSharedSecretResponse {
                    KeyId,
                    SharedSecret,
                    CiphertextForRecipient,
                    KeyAgreementAlgorithm,
                    KeyOrigin,
                } => KeyAgreementAlgorithm,
            }
        }
        pub fn KeyOrigin(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::OriginType>>>{
            match self {
                DeriveSharedSecretResponse::DeriveSharedSecretResponse {
                    KeyId,
                    SharedSecret,
                    CiphertextForRecipient,
                    KeyAgreementAlgorithm,
                    KeyOrigin,
                } => KeyOrigin,
            }
        }
    }

    impl ::std::fmt::Debug for DeriveSharedSecretResponse {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for DeriveSharedSecretResponse {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                DeriveSharedSecretResponse::DeriveSharedSecretResponse {
                    KeyId,
                    SharedSecret,
                    CiphertextForRecipient,
                    KeyAgreementAlgorithm,
                    KeyOrigin,
                } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.DeriveSharedSecretResponse.DeriveSharedSecretResponse(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(KeyId, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(SharedSecret, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(
                        CiphertextForRecipient,
                        _formatter,
                        false,
                    )?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(
                        KeyAgreementAlgorithm,
                        _formatter,
                        false,
                    )?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(KeyOrigin, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for DeriveSharedSecretResponse {}

    impl ::std::hash::Hash for DeriveSharedSecretResponse {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                DeriveSharedSecretResponse::DeriveSharedSecretResponse {
                    KeyId,
                    SharedSecret,
                    CiphertextForRecipient,
                    KeyAgreementAlgorithm,
                    KeyOrigin,
                } => {
                    KeyId.hash(_state);
                    SharedSecret.hash(_state);
                    CiphertextForRecipient.hash(_state);
                    KeyAgreementAlgorithm.hash(_state);
                    KeyOrigin.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for DeriveSharedSecretResponse {
        fn default() -> DeriveSharedSecretResponse {
            DeriveSharedSecretResponse::DeriveSharedSecretResponse {
                KeyId: ::std::default::Default::default(),
                SharedSecret: ::std::default::Default::default(),
                CiphertextForRecipient: ::std::default::Default::default(),
                KeyAgreementAlgorithm: ::std::default::Default::default(),
                KeyOrigin: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<DeriveSharedSecretResponse> for &DeriveSharedSecretResponse {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum EncryptionAlgorithmSpec {
        SYMMETRIC_DEFAULT {},
        RSAES_OAEP_SHA_1 {},
        RSAES_OAEP_SHA_256 {},
    }

    impl EncryptionAlgorithmSpec {}

    impl ::std::fmt::Debug for EncryptionAlgorithmSpec {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for EncryptionAlgorithmSpec {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                EncryptionAlgorithmSpec::SYMMETRIC_DEFAULT {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec.SYMMETRIC__DEFAULT")?;
                    Ok(())
                }
                EncryptionAlgorithmSpec::RSAES_OAEP_SHA_1 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec.RSAES__OAEP__SHA__1")?;
                    Ok(())
                }
                EncryptionAlgorithmSpec::RSAES_OAEP_SHA_256 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.EncryptionAlgorithmSpec.RSAES__OAEP__SHA__256")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for EncryptionAlgorithmSpec {}

    impl ::std::hash::Hash for EncryptionAlgorithmSpec {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                EncryptionAlgorithmSpec::SYMMETRIC_DEFAULT {} => {}
                EncryptionAlgorithmSpec::RSAES_OAEP_SHA_1 {} => {}
                EncryptionAlgorithmSpec::RSAES_OAEP_SHA_256 {} => {}
            }
        }
    }

    impl ::std::default::Default for EncryptionAlgorithmSpec {
        fn default() -> EncryptionAlgorithmSpec {
            EncryptionAlgorithmSpec::SYMMETRIC_DEFAULT {}
        }
    }

    impl ::std::convert::AsRef<EncryptionAlgorithmSpec> for &EncryptionAlgorithmSpec {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum EncryptRequest {
        EncryptRequest {
      KeyId: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
      Plaintext: super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::PlaintextType,
      EncryptionContext: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>>,
      GrantTokens: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GrantTokenList>>,
      EncryptionAlgorithm: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>>,
      DryRun: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>>
    }
  }

    impl EncryptRequest {
        pub fn KeyId(&self) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            match self {
                EncryptRequest::EncryptRequest {
                    KeyId,
                    Plaintext,
                    EncryptionContext,
                    GrantTokens,
                    EncryptionAlgorithm,
                    DryRun,
                } => KeyId,
            }
        }
        pub fn Plaintext(&self) -> &super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::PlaintextType{
            match self {
                EncryptRequest::EncryptRequest {
                    KeyId,
                    Plaintext,
                    EncryptionContext,
                    GrantTokens,
                    EncryptionAlgorithm,
                    DryRun,
                } => Plaintext,
            }
        }
        pub fn EncryptionContext(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Map<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        > {
            match self {
                EncryptRequest::EncryptRequest {
                    KeyId,
                    Plaintext,
                    EncryptionContext,
                    GrantTokens,
                    EncryptionAlgorithm,
                    DryRun,
                } => EncryptionContext,
            }
        }
        pub fn GrantTokens(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GrantTokenList>>{
            match self {
                EncryptRequest::EncryptRequest {
                    KeyId,
                    Plaintext,
                    EncryptionContext,
                    GrantTokens,
                    EncryptionAlgorithm,
                    DryRun,
                } => GrantTokens,
            }
        }
        pub fn EncryptionAlgorithm(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>>{
            match self {
                EncryptRequest::EncryptRequest {
                    KeyId,
                    Plaintext,
                    EncryptionContext,
                    GrantTokens,
                    EncryptionAlgorithm,
                    DryRun,
                } => EncryptionAlgorithm,
            }
        }
        pub fn DryRun(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>> {
            match self {
                EncryptRequest::EncryptRequest {
                    KeyId,
                    Plaintext,
                    EncryptionContext,
                    GrantTokens,
                    EncryptionAlgorithm,
                    DryRun,
                } => DryRun,
            }
        }
    }

    impl ::std::fmt::Debug for EncryptRequest {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for EncryptRequest {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                EncryptRequest::EncryptRequest {
                    KeyId,
                    Plaintext,
                    EncryptionContext,
                    GrantTokens,
                    EncryptionAlgorithm,
                    DryRun,
                } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.EncryptRequest.EncryptRequest(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(KeyId, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(Plaintext, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(EncryptionContext, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(GrantTokens, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(EncryptionAlgorithm, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(DryRun, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for EncryptRequest {}

    impl ::std::hash::Hash for EncryptRequest {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                EncryptRequest::EncryptRequest {
                    KeyId,
                    Plaintext,
                    EncryptionContext,
                    GrantTokens,
                    EncryptionAlgorithm,
                    DryRun,
                } => {
                    KeyId.hash(_state);
                    Plaintext.hash(_state);
                    EncryptionContext.hash(_state);
                    GrantTokens.hash(_state);
                    EncryptionAlgorithm.hash(_state);
                    DryRun.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for EncryptRequest {
        fn default() -> EncryptRequest {
            EncryptRequest::EncryptRequest {
                KeyId: ::std::default::Default::default(),
                Plaintext: ::std::default::Default::default(),
                EncryptionContext: ::std::default::Default::default(),
                GrantTokens: ::std::default::Default::default(),
                EncryptionAlgorithm: ::std::default::Default::default(),
                DryRun: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<EncryptRequest> for &EncryptRequest {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum EncryptResponse {
        EncryptResponse {
      CiphertextBlob: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType>>,
      KeyId: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
      EncryptionAlgorithm: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>>
    }
  }

    impl EncryptResponse {
        pub fn CiphertextBlob(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType>>{
            match self {
                EncryptResponse::EncryptResponse {
                    CiphertextBlob,
                    KeyId,
                    EncryptionAlgorithm,
                } => CiphertextBlob,
            }
        }
        pub fn KeyId(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
                EncryptResponse::EncryptResponse {
                    CiphertextBlob,
                    KeyId,
                    EncryptionAlgorithm,
                } => KeyId,
            }
        }
        pub fn EncryptionAlgorithm(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>>{
            match self {
                EncryptResponse::EncryptResponse {
                    CiphertextBlob,
                    KeyId,
                    EncryptionAlgorithm,
                } => EncryptionAlgorithm,
            }
        }
    }

    impl ::std::fmt::Debug for EncryptResponse {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for EncryptResponse {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                EncryptResponse::EncryptResponse {
                    CiphertextBlob,
                    KeyId,
                    EncryptionAlgorithm,
                } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.EncryptResponse.EncryptResponse(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(CiphertextBlob, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(KeyId, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(EncryptionAlgorithm, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for EncryptResponse {}

    impl ::std::hash::Hash for EncryptResponse {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                EncryptResponse::EncryptResponse {
                    CiphertextBlob,
                    KeyId,
                    EncryptionAlgorithm,
                } => {
                    CiphertextBlob.hash(_state);
                    KeyId.hash(_state);
                    EncryptionAlgorithm.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for EncryptResponse {
        fn default() -> EncryptResponse {
            EncryptResponse::EncryptResponse {
                CiphertextBlob: ::std::default::Default::default(),
                KeyId: ::std::default::Default::default(),
                EncryptionAlgorithm: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<EncryptResponse> for &EncryptResponse {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GenerateDataKeyRequest {
        GenerateDataKeyRequest {
      KeyId: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
      EncryptionContext: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>>,
      NumberOfBytes: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::NumberOfBytesType>>,
      KeySpec: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DataKeySpec>>>,
      GrantTokens: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GrantTokenList>>,
      Recipient: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::RecipientInfo>>>,
      DryRun: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>>
    }
  }

    impl GenerateDataKeyRequest {
        pub fn KeyId(&self) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            match self {
                GenerateDataKeyRequest::GenerateDataKeyRequest {
                    KeyId,
                    EncryptionContext,
                    NumberOfBytes,
                    KeySpec,
                    GrantTokens,
                    Recipient,
                    DryRun,
                } => KeyId,
            }
        }
        pub fn EncryptionContext(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Map<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        > {
            match self {
                GenerateDataKeyRequest::GenerateDataKeyRequest {
                    KeyId,
                    EncryptionContext,
                    NumberOfBytes,
                    KeySpec,
                    GrantTokens,
                    Recipient,
                    DryRun,
                } => EncryptionContext,
            }
        }
        pub fn NumberOfBytes(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::NumberOfBytesType>>{
            match self {
                GenerateDataKeyRequest::GenerateDataKeyRequest {
                    KeyId,
                    EncryptionContext,
                    NumberOfBytes,
                    KeySpec,
                    GrantTokens,
                    Recipient,
                    DryRun,
                } => NumberOfBytes,
            }
        }
        pub fn KeySpec(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DataKeySpec>>>{
            match self {
                GenerateDataKeyRequest::GenerateDataKeyRequest {
                    KeyId,
                    EncryptionContext,
                    NumberOfBytes,
                    KeySpec,
                    GrantTokens,
                    Recipient,
                    DryRun,
                } => KeySpec,
            }
        }
        pub fn GrantTokens(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GrantTokenList>>{
            match self {
                GenerateDataKeyRequest::GenerateDataKeyRequest {
                    KeyId,
                    EncryptionContext,
                    NumberOfBytes,
                    KeySpec,
                    GrantTokens,
                    Recipient,
                    DryRun,
                } => GrantTokens,
            }
        }
        pub fn Recipient(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::RecipientInfo>>>{
            match self {
                GenerateDataKeyRequest::GenerateDataKeyRequest {
                    KeyId,
                    EncryptionContext,
                    NumberOfBytes,
                    KeySpec,
                    GrantTokens,
                    Recipient,
                    DryRun,
                } => Recipient,
            }
        }
        pub fn DryRun(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>> {
            match self {
                GenerateDataKeyRequest::GenerateDataKeyRequest {
                    KeyId,
                    EncryptionContext,
                    NumberOfBytes,
                    KeySpec,
                    GrantTokens,
                    Recipient,
                    DryRun,
                } => DryRun,
            }
        }
    }

    impl ::std::fmt::Debug for GenerateDataKeyRequest {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GenerateDataKeyRequest {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GenerateDataKeyRequest::GenerateDataKeyRequest {
                    KeyId,
                    EncryptionContext,
                    NumberOfBytes,
                    KeySpec,
                    GrantTokens,
                    Recipient,
                    DryRun,
                } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyRequest.GenerateDataKeyRequest(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(KeyId, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(EncryptionContext, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(NumberOfBytes, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(KeySpec, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(GrantTokens, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(Recipient, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(DryRun, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GenerateDataKeyRequest {}

    impl ::std::hash::Hash for GenerateDataKeyRequest {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GenerateDataKeyRequest::GenerateDataKeyRequest {
                    KeyId,
                    EncryptionContext,
                    NumberOfBytes,
                    KeySpec,
                    GrantTokens,
                    Recipient,
                    DryRun,
                } => {
                    KeyId.hash(_state);
                    EncryptionContext.hash(_state);
                    NumberOfBytes.hash(_state);
                    KeySpec.hash(_state);
                    GrantTokens.hash(_state);
                    Recipient.hash(_state);
                    DryRun.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for GenerateDataKeyRequest {
        fn default() -> GenerateDataKeyRequest {
            GenerateDataKeyRequest::GenerateDataKeyRequest {
                KeyId: ::std::default::Default::default(),
                EncryptionContext: ::std::default::Default::default(),
                NumberOfBytes: ::std::default::Default::default(),
                KeySpec: ::std::default::Default::default(),
                GrantTokens: ::std::default::Default::default(),
                Recipient: ::std::default::Default::default(),
                DryRun: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GenerateDataKeyRequest> for &GenerateDataKeyRequest {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GenerateDataKeyResponse {
        GenerateDataKeyResponse {
      CiphertextBlob: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType>>,
      Plaintext: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::PlaintextType>>,
      KeyId: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
      CiphertextForRecipient: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType>>
    }
  }

    impl GenerateDataKeyResponse {
        pub fn CiphertextBlob(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType>>{
            match self {
                GenerateDataKeyResponse::GenerateDataKeyResponse {
                    CiphertextBlob,
                    Plaintext,
                    KeyId,
                    CiphertextForRecipient,
                } => CiphertextBlob,
            }
        }
        pub fn Plaintext(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::PlaintextType>>{
            match self {
                GenerateDataKeyResponse::GenerateDataKeyResponse {
                    CiphertextBlob,
                    Plaintext,
                    KeyId,
                    CiphertextForRecipient,
                } => Plaintext,
            }
        }
        pub fn KeyId(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
                GenerateDataKeyResponse::GenerateDataKeyResponse {
                    CiphertextBlob,
                    Plaintext,
                    KeyId,
                    CiphertextForRecipient,
                } => KeyId,
            }
        }
        pub fn CiphertextForRecipient(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType>>{
            match self {
                GenerateDataKeyResponse::GenerateDataKeyResponse {
                    CiphertextBlob,
                    Plaintext,
                    KeyId,
                    CiphertextForRecipient,
                } => CiphertextForRecipient,
            }
        }
    }

    impl ::std::fmt::Debug for GenerateDataKeyResponse {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GenerateDataKeyResponse {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GenerateDataKeyResponse::GenerateDataKeyResponse {
                    CiphertextBlob,
                    Plaintext,
                    KeyId,
                    CiphertextForRecipient,
                } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyResponse.GenerateDataKeyResponse(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(CiphertextBlob, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(Plaintext, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(KeyId, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(
                        CiphertextForRecipient,
                        _formatter,
                        false,
                    )?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GenerateDataKeyResponse {}

    impl ::std::hash::Hash for GenerateDataKeyResponse {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GenerateDataKeyResponse::GenerateDataKeyResponse {
                    CiphertextBlob,
                    Plaintext,
                    KeyId,
                    CiphertextForRecipient,
                } => {
                    CiphertextBlob.hash(_state);
                    Plaintext.hash(_state);
                    KeyId.hash(_state);
                    CiphertextForRecipient.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for GenerateDataKeyResponse {
        fn default() -> GenerateDataKeyResponse {
            GenerateDataKeyResponse::GenerateDataKeyResponse {
                CiphertextBlob: ::std::default::Default::default(),
                Plaintext: ::std::default::Default::default(),
                KeyId: ::std::default::Default::default(),
                CiphertextForRecipient: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GenerateDataKeyResponse> for &GenerateDataKeyResponse {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GenerateDataKeyWithoutPlaintextRequest {
        GenerateDataKeyWithoutPlaintextRequest {
      KeyId: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
      EncryptionContext: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>>,
      KeySpec: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DataKeySpec>>>,
      NumberOfBytes: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::NumberOfBytesType>>,
      GrantTokens: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GrantTokenList>>,
      DryRun: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>>
    }
  }

    impl GenerateDataKeyWithoutPlaintextRequest {
        pub fn KeyId(&self) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            match self {
        GenerateDataKeyWithoutPlaintextRequest::GenerateDataKeyWithoutPlaintextRequest{KeyId, EncryptionContext, KeySpec, NumberOfBytes, GrantTokens, DryRun, } => KeyId,
      }
        }
        pub fn EncryptionContext(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Map<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        > {
            match self {
        GenerateDataKeyWithoutPlaintextRequest::GenerateDataKeyWithoutPlaintextRequest{KeyId, EncryptionContext, KeySpec, NumberOfBytes, GrantTokens, DryRun, } => EncryptionContext,
      }
        }
        pub fn KeySpec(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DataKeySpec>>>{
            match self {
        GenerateDataKeyWithoutPlaintextRequest::GenerateDataKeyWithoutPlaintextRequest{KeyId, EncryptionContext, KeySpec, NumberOfBytes, GrantTokens, DryRun, } => KeySpec,
      }
        }
        pub fn NumberOfBytes(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::NumberOfBytesType>>{
            match self {
        GenerateDataKeyWithoutPlaintextRequest::GenerateDataKeyWithoutPlaintextRequest{KeyId, EncryptionContext, KeySpec, NumberOfBytes, GrantTokens, DryRun, } => NumberOfBytes,
      }
        }
        pub fn GrantTokens(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GrantTokenList>>{
            match self {
        GenerateDataKeyWithoutPlaintextRequest::GenerateDataKeyWithoutPlaintextRequest{KeyId, EncryptionContext, KeySpec, NumberOfBytes, GrantTokens, DryRun, } => GrantTokens,
      }
        }
        pub fn DryRun(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>> {
            match self {
        GenerateDataKeyWithoutPlaintextRequest::GenerateDataKeyWithoutPlaintextRequest{KeyId, EncryptionContext, KeySpec, NumberOfBytes, GrantTokens, DryRun, } => DryRun,
      }
        }
    }

    impl ::std::fmt::Debug for GenerateDataKeyWithoutPlaintextRequest {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GenerateDataKeyWithoutPlaintextRequest {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
        GenerateDataKeyWithoutPlaintextRequest::GenerateDataKeyWithoutPlaintextRequest{KeyId, EncryptionContext, KeySpec, NumberOfBytes, GrantTokens, DryRun, } => {
          write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyWithoutPlaintextRequest.GenerateDataKeyWithoutPlaintextRequest(")?;
          ::dafny_runtime::DafnyPrint::fmt_print(KeyId, _formatter, false)?;
          write!(_formatter, ", ")?;
          ::dafny_runtime::DafnyPrint::fmt_print(EncryptionContext, _formatter, false)?;
          write!(_formatter, ", ")?;
          ::dafny_runtime::DafnyPrint::fmt_print(KeySpec, _formatter, false)?;
          write!(_formatter, ", ")?;
          ::dafny_runtime::DafnyPrint::fmt_print(NumberOfBytes, _formatter, false)?;
          write!(_formatter, ", ")?;
          ::dafny_runtime::DafnyPrint::fmt_print(GrantTokens, _formatter, false)?;
          write!(_formatter, ", ")?;
          ::dafny_runtime::DafnyPrint::fmt_print(DryRun, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
      }
        }
    }

    impl Eq for GenerateDataKeyWithoutPlaintextRequest {}

    impl ::std::hash::Hash for GenerateDataKeyWithoutPlaintextRequest {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
        GenerateDataKeyWithoutPlaintextRequest::GenerateDataKeyWithoutPlaintextRequest{KeyId, EncryptionContext, KeySpec, NumberOfBytes, GrantTokens, DryRun, } => {
          KeyId.hash(_state);
          EncryptionContext.hash(_state);
          KeySpec.hash(_state);
          NumberOfBytes.hash(_state);
          GrantTokens.hash(_state);
          DryRun.hash(_state)
        },
      }
        }
    }

    impl ::std::default::Default for GenerateDataKeyWithoutPlaintextRequest {
        fn default() -> GenerateDataKeyWithoutPlaintextRequest {
            GenerateDataKeyWithoutPlaintextRequest::GenerateDataKeyWithoutPlaintextRequest {
                KeyId: ::std::default::Default::default(),
                EncryptionContext: ::std::default::Default::default(),
                KeySpec: ::std::default::Default::default(),
                NumberOfBytes: ::std::default::Default::default(),
                GrantTokens: ::std::default::Default::default(),
                DryRun: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GenerateDataKeyWithoutPlaintextRequest>
        for &GenerateDataKeyWithoutPlaintextRequest
    {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GenerateDataKeyWithoutPlaintextResponse {
        GenerateDataKeyWithoutPlaintextResponse {
      CiphertextBlob: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType>>,
      KeyId: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>
    }
  }

    impl GenerateDataKeyWithoutPlaintextResponse {
        pub fn CiphertextBlob(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType>>{
            match self {
        GenerateDataKeyWithoutPlaintextResponse::GenerateDataKeyWithoutPlaintextResponse{CiphertextBlob, KeyId, } => CiphertextBlob,
      }
        }
        pub fn KeyId(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
        GenerateDataKeyWithoutPlaintextResponse::GenerateDataKeyWithoutPlaintextResponse{CiphertextBlob, KeyId, } => KeyId,
      }
        }
    }

    impl ::std::fmt::Debug for GenerateDataKeyWithoutPlaintextResponse {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GenerateDataKeyWithoutPlaintextResponse {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
        GenerateDataKeyWithoutPlaintextResponse::GenerateDataKeyWithoutPlaintextResponse{CiphertextBlob, KeyId, } => {
          write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.GenerateDataKeyWithoutPlaintextResponse.GenerateDataKeyWithoutPlaintextResponse(")?;
          ::dafny_runtime::DafnyPrint::fmt_print(CiphertextBlob, _formatter, false)?;
          write!(_formatter, ", ")?;
          ::dafny_runtime::DafnyPrint::fmt_print(KeyId, _formatter, false)?;
          write!(_formatter, ")")?;
          Ok(())
        },
      }
        }
    }

    impl Eq for GenerateDataKeyWithoutPlaintextResponse {}

    impl ::std::hash::Hash for GenerateDataKeyWithoutPlaintextResponse {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
        GenerateDataKeyWithoutPlaintextResponse::GenerateDataKeyWithoutPlaintextResponse{CiphertextBlob, KeyId, } => {
          CiphertextBlob.hash(_state);
          KeyId.hash(_state)
        },
      }
        }
    }

    impl ::std::default::Default for GenerateDataKeyWithoutPlaintextResponse {
        fn default() -> GenerateDataKeyWithoutPlaintextResponse {
            GenerateDataKeyWithoutPlaintextResponse::GenerateDataKeyWithoutPlaintextResponse {
                CiphertextBlob: ::std::default::Default::default(),
                KeyId: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GenerateDataKeyWithoutPlaintextResponse>
        for &GenerateDataKeyWithoutPlaintextResponse
    {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GetPublicKeyRequest {
        GetPublicKeyRequest {
      KeyId: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
      GrantTokens: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GrantTokenList>>
    }
  }

    impl GetPublicKeyRequest {
        pub fn KeyId(&self) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            match self {
                GetPublicKeyRequest::GetPublicKeyRequest { KeyId, GrantTokens } => KeyId,
            }
        }
        pub fn GrantTokens(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GrantTokenList>>{
            match self {
                GetPublicKeyRequest::GetPublicKeyRequest { KeyId, GrantTokens } => GrantTokens,
            }
        }
    }

    impl ::std::fmt::Debug for GetPublicKeyRequest {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetPublicKeyRequest {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetPublicKeyRequest::GetPublicKeyRequest { KeyId, GrantTokens } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.GetPublicKeyRequest.GetPublicKeyRequest(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(KeyId, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(GrantTokens, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetPublicKeyRequest {}

    impl ::std::hash::Hash for GetPublicKeyRequest {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetPublicKeyRequest::GetPublicKeyRequest { KeyId, GrantTokens } => {
                    KeyId.hash(_state);
                    GrantTokens.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for GetPublicKeyRequest {
        fn default() -> GetPublicKeyRequest {
            GetPublicKeyRequest::GetPublicKeyRequest {
                KeyId: ::std::default::Default::default(),
                GrantTokens: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetPublicKeyRequest> for &GetPublicKeyRequest {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum GetPublicKeyResponse {
        GetPublicKeyResponse {
      KeyId: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
      PublicKey: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::PublicKeyType>>,
      CustomerMasterKeySpec: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CustomerMasterKeySpec>>>,
      KeySpec: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec>>>,
      KeyUsage: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyUsageType>>>,
      EncryptionAlgorithms: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>>>,
      SigningAlgorithms: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::SigningAlgorithmSpec>>>>,
      KeyAgreementAlgorithms: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyAgreementAlgorithmSpec>>>>
    }
  }

    impl GetPublicKeyResponse {
        pub fn KeyId(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
                GetPublicKeyResponse::GetPublicKeyResponse {
                    KeyId,
                    PublicKey,
                    CustomerMasterKeySpec,
                    KeySpec,
                    KeyUsage,
                    EncryptionAlgorithms,
                    SigningAlgorithms,
                    KeyAgreementAlgorithms,
                } => KeyId,
            }
        }
        pub fn PublicKey(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::PublicKeyType>>{
            match self {
                GetPublicKeyResponse::GetPublicKeyResponse {
                    KeyId,
                    PublicKey,
                    CustomerMasterKeySpec,
                    KeySpec,
                    KeyUsage,
                    EncryptionAlgorithms,
                    SigningAlgorithms,
                    KeyAgreementAlgorithms,
                } => PublicKey,
            }
        }
        pub fn CustomerMasterKeySpec(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CustomerMasterKeySpec>>>{
            match self {
                GetPublicKeyResponse::GetPublicKeyResponse {
                    KeyId,
                    PublicKey,
                    CustomerMasterKeySpec,
                    KeySpec,
                    KeyUsage,
                    EncryptionAlgorithms,
                    SigningAlgorithms,
                    KeyAgreementAlgorithms,
                } => CustomerMasterKeySpec,
            }
        }
        pub fn KeySpec(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec>>>{
            match self {
                GetPublicKeyResponse::GetPublicKeyResponse {
                    KeyId,
                    PublicKey,
                    CustomerMasterKeySpec,
                    KeySpec,
                    KeyUsage,
                    EncryptionAlgorithms,
                    SigningAlgorithms,
                    KeyAgreementAlgorithms,
                } => KeySpec,
            }
        }
        pub fn KeyUsage(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyUsageType>>>{
            match self {
                GetPublicKeyResponse::GetPublicKeyResponse {
                    KeyId,
                    PublicKey,
                    CustomerMasterKeySpec,
                    KeySpec,
                    KeyUsage,
                    EncryptionAlgorithms,
                    SigningAlgorithms,
                    KeyAgreementAlgorithms,
                } => KeyUsage,
            }
        }
        pub fn EncryptionAlgorithms(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>>>{
            match self {
                GetPublicKeyResponse::GetPublicKeyResponse {
                    KeyId,
                    PublicKey,
                    CustomerMasterKeySpec,
                    KeySpec,
                    KeyUsage,
                    EncryptionAlgorithms,
                    SigningAlgorithms,
                    KeyAgreementAlgorithms,
                } => EncryptionAlgorithms,
            }
        }
        pub fn SigningAlgorithms(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::SigningAlgorithmSpec>>>>{
            match self {
                GetPublicKeyResponse::GetPublicKeyResponse {
                    KeyId,
                    PublicKey,
                    CustomerMasterKeySpec,
                    KeySpec,
                    KeyUsage,
                    EncryptionAlgorithms,
                    SigningAlgorithms,
                    KeyAgreementAlgorithms,
                } => SigningAlgorithms,
            }
        }
        pub fn KeyAgreementAlgorithms(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyAgreementAlgorithmSpec>>>>{
            match self {
                GetPublicKeyResponse::GetPublicKeyResponse {
                    KeyId,
                    PublicKey,
                    CustomerMasterKeySpec,
                    KeySpec,
                    KeyUsage,
                    EncryptionAlgorithms,
                    SigningAlgorithms,
                    KeyAgreementAlgorithms,
                } => KeyAgreementAlgorithms,
            }
        }
    }

    impl ::std::fmt::Debug for GetPublicKeyResponse {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for GetPublicKeyResponse {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                GetPublicKeyResponse::GetPublicKeyResponse {
                    KeyId,
                    PublicKey,
                    CustomerMasterKeySpec,
                    KeySpec,
                    KeyUsage,
                    EncryptionAlgorithms,
                    SigningAlgorithms,
                    KeyAgreementAlgorithms,
                } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.GetPublicKeyResponse.GetPublicKeyResponse(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(KeyId, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(PublicKey, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(
                        CustomerMasterKeySpec,
                        _formatter,
                        false,
                    )?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(KeySpec, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(KeyUsage, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(
                        EncryptionAlgorithms,
                        _formatter,
                        false,
                    )?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(SigningAlgorithms, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(
                        KeyAgreementAlgorithms,
                        _formatter,
                        false,
                    )?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for GetPublicKeyResponse {}

    impl ::std::hash::Hash for GetPublicKeyResponse {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                GetPublicKeyResponse::GetPublicKeyResponse {
                    KeyId,
                    PublicKey,
                    CustomerMasterKeySpec,
                    KeySpec,
                    KeyUsage,
                    EncryptionAlgorithms,
                    SigningAlgorithms,
                    KeyAgreementAlgorithms,
                } => {
                    KeyId.hash(_state);
                    PublicKey.hash(_state);
                    CustomerMasterKeySpec.hash(_state);
                    KeySpec.hash(_state);
                    KeyUsage.hash(_state);
                    EncryptionAlgorithms.hash(_state);
                    SigningAlgorithms.hash(_state);
                    KeyAgreementAlgorithms.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for GetPublicKeyResponse {
        fn default() -> GetPublicKeyResponse {
            GetPublicKeyResponse::GetPublicKeyResponse {
                KeyId: ::std::default::Default::default(),
                PublicKey: ::std::default::Default::default(),
                CustomerMasterKeySpec: ::std::default::Default::default(),
                KeySpec: ::std::default::Default::default(),
                KeyUsage: ::std::default::Default::default(),
                EncryptionAlgorithms: ::std::default::Default::default(),
                SigningAlgorithms: ::std::default::Default::default(),
                KeyAgreementAlgorithms: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<GetPublicKeyResponse> for &GetPublicKeyResponse {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub type GrantTokenList =
        ::dafny_runtime::Sequence<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>;

    pub type GrantTokenType = ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>;

    #[derive(PartialEq, Clone)]
    pub enum KeyAgreementAlgorithmSpec {
        ECDH {},
    }

    impl KeyAgreementAlgorithmSpec {}

    impl ::std::fmt::Debug for KeyAgreementAlgorithmSpec {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for KeyAgreementAlgorithmSpec {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                KeyAgreementAlgorithmSpec::ECDH {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeyAgreementAlgorithmSpec.ECDH")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for KeyAgreementAlgorithmSpec {}

    impl ::std::hash::Hash for KeyAgreementAlgorithmSpec {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                KeyAgreementAlgorithmSpec::ECDH {} => {}
            }
        }
    }

    impl ::std::default::Default for KeyAgreementAlgorithmSpec {
        fn default() -> KeyAgreementAlgorithmSpec {
            KeyAgreementAlgorithmSpec::ECDH {}
        }
    }

    impl ::std::convert::AsRef<KeyAgreementAlgorithmSpec> for &KeyAgreementAlgorithmSpec {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum KeyEncryptionMechanism {
        RSAES_OAEP_SHA_256 {},
    }

    impl KeyEncryptionMechanism {}

    impl ::std::fmt::Debug for KeyEncryptionMechanism {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for KeyEncryptionMechanism {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                KeyEncryptionMechanism::RSAES_OAEP_SHA_256 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeyEncryptionMechanism.RSAES__OAEP__SHA__256")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for KeyEncryptionMechanism {}

    impl ::std::hash::Hash for KeyEncryptionMechanism {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                KeyEncryptionMechanism::RSAES_OAEP_SHA_256 {} => {}
            }
        }
    }

    impl ::std::default::Default for KeyEncryptionMechanism {
        fn default() -> KeyEncryptionMechanism {
            KeyEncryptionMechanism::RSAES_OAEP_SHA_256 {}
        }
    }

    impl ::std::convert::AsRef<KeyEncryptionMechanism> for &KeyEncryptionMechanism {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub type KeyIdType = ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>;

    #[derive(PartialEq, Clone)]
    pub enum KeySpec {
        RSA_2048 {},
        RSA_3072 {},
        RSA_4096 {},
        ECC_NIST_P256 {},
        ECC_NIST_P384 {},
        ECC_NIST_P521 {},
        ECC_SECG_P256K1 {},
        SYMMETRIC_DEFAULT {},
        HMAC_224 {},
        HMAC_256 {},
        HMAC_384 {},
        HMAC_512 {},
        SM2 {},
    }

    impl KeySpec {}

    impl ::std::fmt::Debug for KeySpec {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for KeySpec {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                KeySpec::RSA_2048 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.RSA__2048")?;
                    Ok(())
                }
                KeySpec::RSA_3072 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.RSA__3072")?;
                    Ok(())
                }
                KeySpec::RSA_4096 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.RSA__4096")?;
                    Ok(())
                }
                KeySpec::ECC_NIST_P256 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.ECC__NIST__P256")?;
                    Ok(())
                }
                KeySpec::ECC_NIST_P384 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.ECC__NIST__P384")?;
                    Ok(())
                }
                KeySpec::ECC_NIST_P521 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.ECC__NIST__P521")?;
                    Ok(())
                }
                KeySpec::ECC_SECG_P256K1 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.ECC__SECG__P256K1")?;
                    Ok(())
                }
                KeySpec::SYMMETRIC_DEFAULT {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.SYMMETRIC__DEFAULT")?;
                    Ok(())
                }
                KeySpec::HMAC_224 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.HMAC__224")?;
                    Ok(())
                }
                KeySpec::HMAC_256 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.HMAC__256")?;
                    Ok(())
                }
                KeySpec::HMAC_384 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.HMAC__384")?;
                    Ok(())
                }
                KeySpec::HMAC_512 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.HMAC__512")?;
                    Ok(())
                }
                KeySpec::SM2 {} => {
                    write!(
                        _formatter,
                        "software.amazon.cryptography.services.kms.internaldafny.types.KeySpec.SM2"
                    )?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for KeySpec {}

    impl ::std::hash::Hash for KeySpec {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                KeySpec::RSA_2048 {} => {}
                KeySpec::RSA_3072 {} => {}
                KeySpec::RSA_4096 {} => {}
                KeySpec::ECC_NIST_P256 {} => {}
                KeySpec::ECC_NIST_P384 {} => {}
                KeySpec::ECC_NIST_P521 {} => {}
                KeySpec::ECC_SECG_P256K1 {} => {}
                KeySpec::SYMMETRIC_DEFAULT {} => {}
                KeySpec::HMAC_224 {} => {}
                KeySpec::HMAC_256 {} => {}
                KeySpec::HMAC_384 {} => {}
                KeySpec::HMAC_512 {} => {}
                KeySpec::SM2 {} => {}
            }
        }
    }

    impl ::std::default::Default for KeySpec {
        fn default() -> KeySpec {
            KeySpec::RSA_2048 {}
        }
    }

    impl ::std::convert::AsRef<KeySpec> for &KeySpec {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum KeyUsageType {
        SIGN_VERIFY {},
        ENCRYPT_DECRYPT {},
        GENERATE_VERIFY_MAC {},
        KEY_AGREEMENT {},
    }

    impl KeyUsageType {}

    impl ::std::fmt::Debug for KeyUsageType {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for KeyUsageType {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                KeyUsageType::SIGN_VERIFY {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType.SIGN__VERIFY")?;
                    Ok(())
                }
                KeyUsageType::ENCRYPT_DECRYPT {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType.ENCRYPT__DECRYPT")?;
                    Ok(())
                }
                KeyUsageType::GENERATE_VERIFY_MAC {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType.GENERATE__VERIFY__MAC")?;
                    Ok(())
                }
                KeyUsageType::KEY_AGREEMENT {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.KeyUsageType.KEY__AGREEMENT")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for KeyUsageType {}

    impl ::std::hash::Hash for KeyUsageType {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                KeyUsageType::SIGN_VERIFY {} => {}
                KeyUsageType::ENCRYPT_DECRYPT {} => {}
                KeyUsageType::GENERATE_VERIFY_MAC {} => {}
                KeyUsageType::KEY_AGREEMENT {} => {}
            }
        }
    }

    impl ::std::default::Default for KeyUsageType {
        fn default() -> KeyUsageType {
            KeyUsageType::SIGN_VERIFY {}
        }
    }

    impl ::std::convert::AsRef<KeyUsageType> for &KeyUsageType {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub type NumberOfBytesType = i32;

    #[derive(PartialEq, Clone)]
    pub enum OriginType {
        AWS_KMS {},
        EXTERNAL {},
        AWS_CLOUDHSM {},
        EXTERNAL_KEY_STORE {},
    }

    impl OriginType {}

    impl ::std::fmt::Debug for OriginType {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for OriginType {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                OriginType::AWS_KMS {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.OriginType.AWS__KMS")?;
                    Ok(())
                }
                OriginType::EXTERNAL {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.OriginType.EXTERNAL")?;
                    Ok(())
                }
                OriginType::AWS_CLOUDHSM {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.OriginType.AWS__CLOUDHSM")?;
                    Ok(())
                }
                OriginType::EXTERNAL_KEY_STORE {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.OriginType.EXTERNAL__KEY__STORE")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for OriginType {}

    impl ::std::hash::Hash for OriginType {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                OriginType::AWS_KMS {} => {}
                OriginType::EXTERNAL {} => {}
                OriginType::AWS_CLOUDHSM {} => {}
                OriginType::EXTERNAL_KEY_STORE {} => {}
            }
        }
    }

    impl ::std::default::Default for OriginType {
        fn default() -> OriginType {
            OriginType::AWS_KMS {}
        }
    }

    impl ::std::convert::AsRef<OriginType> for &OriginType {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub type PlaintextType = ::dafny_runtime::Sequence<u8>;

    pub type PublicKeyType = ::dafny_runtime::Sequence<u8>;

    #[derive(PartialEq, Clone)]
    pub enum RecipientInfo {
        RecipientInfo {
      KeyEncryptionAlgorithm: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyEncryptionMechanism>>>,
      AttestationDocument: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::AttestationDocumentType>>
    }
  }

    impl RecipientInfo {
        pub fn KeyEncryptionAlgorithm(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyEncryptionMechanism>>>{
            match self {
                RecipientInfo::RecipientInfo {
                    KeyEncryptionAlgorithm,
                    AttestationDocument,
                } => KeyEncryptionAlgorithm,
            }
        }
        pub fn AttestationDocument(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::AttestationDocumentType>>{
            match self {
                RecipientInfo::RecipientInfo {
                    KeyEncryptionAlgorithm,
                    AttestationDocument,
                } => AttestationDocument,
            }
        }
    }

    impl ::std::fmt::Debug for RecipientInfo {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for RecipientInfo {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                RecipientInfo::RecipientInfo {
                    KeyEncryptionAlgorithm,
                    AttestationDocument,
                } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.RecipientInfo.RecipientInfo(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(
                        KeyEncryptionAlgorithm,
                        _formatter,
                        false,
                    )?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(AttestationDocument, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for RecipientInfo {}

    impl ::std::hash::Hash for RecipientInfo {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                RecipientInfo::RecipientInfo {
                    KeyEncryptionAlgorithm,
                    AttestationDocument,
                } => {
                    KeyEncryptionAlgorithm.hash(_state);
                    AttestationDocument.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for RecipientInfo {
        fn default() -> RecipientInfo {
            RecipientInfo::RecipientInfo {
                KeyEncryptionAlgorithm: ::std::default::Default::default(),
                AttestationDocument: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<RecipientInfo> for &RecipientInfo {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum ReEncryptRequest {
        ReEncryptRequest {
      CiphertextBlob: super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType,
      SourceEncryptionContext: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>>,
      SourceKeyId: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
      DestinationKeyId: ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
      DestinationEncryptionContext: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Map<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>, ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>>,
      SourceEncryptionAlgorithm: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>>,
      DestinationEncryptionAlgorithm: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>>,
      GrantTokens: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GrantTokenList>>,
      DryRun: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>>
    }
  }

    impl ReEncryptRequest {
        pub fn CiphertextBlob(&self) -> &super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType{
            match self {
                ReEncryptRequest::ReEncryptRequest {
                    CiphertextBlob,
                    SourceEncryptionContext,
                    SourceKeyId,
                    DestinationKeyId,
                    DestinationEncryptionContext,
                    SourceEncryptionAlgorithm,
                    DestinationEncryptionAlgorithm,
                    GrantTokens,
                    DryRun,
                } => CiphertextBlob,
            }
        }
        pub fn SourceEncryptionContext(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Map<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        > {
            match self {
                ReEncryptRequest::ReEncryptRequest {
                    CiphertextBlob,
                    SourceEncryptionContext,
                    SourceKeyId,
                    DestinationKeyId,
                    DestinationEncryptionContext,
                    SourceEncryptionAlgorithm,
                    DestinationEncryptionAlgorithm,
                    GrantTokens,
                    DryRun,
                } => SourceEncryptionContext,
            }
        }
        pub fn SourceKeyId(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
                ReEncryptRequest::ReEncryptRequest {
                    CiphertextBlob,
                    SourceEncryptionContext,
                    SourceKeyId,
                    DestinationKeyId,
                    DestinationEncryptionContext,
                    SourceEncryptionAlgorithm,
                    DestinationEncryptionAlgorithm,
                    GrantTokens,
                    DryRun,
                } => SourceKeyId,
            }
        }
        pub fn DestinationKeyId(
            &self,
        ) -> &::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16> {
            match self {
                ReEncryptRequest::ReEncryptRequest {
                    CiphertextBlob,
                    SourceEncryptionContext,
                    SourceKeyId,
                    DestinationKeyId,
                    DestinationEncryptionContext,
                    SourceEncryptionAlgorithm,
                    DestinationEncryptionAlgorithm,
                    GrantTokens,
                    DryRun,
                } => DestinationKeyId,
            }
        }
        pub fn DestinationEncryptionContext(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Map<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        > {
            match self {
                ReEncryptRequest::ReEncryptRequest {
                    CiphertextBlob,
                    SourceEncryptionContext,
                    SourceKeyId,
                    DestinationKeyId,
                    DestinationEncryptionContext,
                    SourceEncryptionAlgorithm,
                    DestinationEncryptionAlgorithm,
                    GrantTokens,
                    DryRun,
                } => DestinationEncryptionContext,
            }
        }
        pub fn SourceEncryptionAlgorithm(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>>{
            match self {
                ReEncryptRequest::ReEncryptRequest {
                    CiphertextBlob,
                    SourceEncryptionContext,
                    SourceKeyId,
                    DestinationKeyId,
                    DestinationEncryptionContext,
                    SourceEncryptionAlgorithm,
                    DestinationEncryptionAlgorithm,
                    GrantTokens,
                    DryRun,
                } => SourceEncryptionAlgorithm,
            }
        }
        pub fn DestinationEncryptionAlgorithm(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>>{
            match self {
                ReEncryptRequest::ReEncryptRequest {
                    CiphertextBlob,
                    SourceEncryptionContext,
                    SourceKeyId,
                    DestinationKeyId,
                    DestinationEncryptionContext,
                    SourceEncryptionAlgorithm,
                    DestinationEncryptionAlgorithm,
                    GrantTokens,
                    DryRun,
                } => DestinationEncryptionAlgorithm,
            }
        }
        pub fn GrantTokens(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GrantTokenList>>{
            match self {
                ReEncryptRequest::ReEncryptRequest {
                    CiphertextBlob,
                    SourceEncryptionContext,
                    SourceKeyId,
                    DestinationKeyId,
                    DestinationEncryptionContext,
                    SourceEncryptionAlgorithm,
                    DestinationEncryptionAlgorithm,
                    GrantTokens,
                    DryRun,
                } => GrantTokens,
            }
        }
        pub fn DryRun(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<bool>> {
            match self {
                ReEncryptRequest::ReEncryptRequest {
                    CiphertextBlob,
                    SourceEncryptionContext,
                    SourceKeyId,
                    DestinationKeyId,
                    DestinationEncryptionContext,
                    SourceEncryptionAlgorithm,
                    DestinationEncryptionAlgorithm,
                    GrantTokens,
                    DryRun,
                } => DryRun,
            }
        }
    }

    impl ::std::fmt::Debug for ReEncryptRequest {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for ReEncryptRequest {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                ReEncryptRequest::ReEncryptRequest {
                    CiphertextBlob,
                    SourceEncryptionContext,
                    SourceKeyId,
                    DestinationKeyId,
                    DestinationEncryptionContext,
                    SourceEncryptionAlgorithm,
                    DestinationEncryptionAlgorithm,
                    GrantTokens,
                    DryRun,
                } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.ReEncryptRequest.ReEncryptRequest(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(CiphertextBlob, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(
                        SourceEncryptionContext,
                        _formatter,
                        false,
                    )?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(SourceKeyId, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(DestinationKeyId, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(
                        DestinationEncryptionContext,
                        _formatter,
                        false,
                    )?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(
                        SourceEncryptionAlgorithm,
                        _formatter,
                        false,
                    )?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(
                        DestinationEncryptionAlgorithm,
                        _formatter,
                        false,
                    )?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(GrantTokens, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(DryRun, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for ReEncryptRequest {}

    impl ::std::hash::Hash for ReEncryptRequest {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                ReEncryptRequest::ReEncryptRequest {
                    CiphertextBlob,
                    SourceEncryptionContext,
                    SourceKeyId,
                    DestinationKeyId,
                    DestinationEncryptionContext,
                    SourceEncryptionAlgorithm,
                    DestinationEncryptionAlgorithm,
                    GrantTokens,
                    DryRun,
                } => {
                    CiphertextBlob.hash(_state);
                    SourceEncryptionContext.hash(_state);
                    SourceKeyId.hash(_state);
                    DestinationKeyId.hash(_state);
                    DestinationEncryptionContext.hash(_state);
                    SourceEncryptionAlgorithm.hash(_state);
                    DestinationEncryptionAlgorithm.hash(_state);
                    GrantTokens.hash(_state);
                    DryRun.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for ReEncryptRequest {
        fn default() -> ReEncryptRequest {
            ReEncryptRequest::ReEncryptRequest {
                CiphertextBlob: ::std::default::Default::default(),
                SourceEncryptionContext: ::std::default::Default::default(),
                SourceKeyId: ::std::default::Default::default(),
                DestinationKeyId: ::std::default::Default::default(),
                DestinationEncryptionContext: ::std::default::Default::default(),
                SourceEncryptionAlgorithm: ::std::default::Default::default(),
                DestinationEncryptionAlgorithm: ::std::default::Default::default(),
                GrantTokens: ::std::default::Default::default(),
                DryRun: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<ReEncryptRequest> for &ReEncryptRequest {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum ReEncryptResponse {
        ReEncryptResponse {
      CiphertextBlob: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType>>,
      SourceKeyId: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
      KeyId: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>>,
      SourceEncryptionAlgorithm: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>>,
      DestinationEncryptionAlgorithm: ::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>>
    }
  }

    impl ReEncryptResponse {
        pub fn CiphertextBlob(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::CiphertextType>>{
            match self {
                ReEncryptResponse::ReEncryptResponse {
                    CiphertextBlob,
                    SourceKeyId,
                    KeyId,
                    SourceEncryptionAlgorithm,
                    DestinationEncryptionAlgorithm,
                } => CiphertextBlob,
            }
        }
        pub fn SourceKeyId(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
                ReEncryptResponse::ReEncryptResponse {
                    CiphertextBlob,
                    SourceKeyId,
                    KeyId,
                    SourceEncryptionAlgorithm,
                    DestinationEncryptionAlgorithm,
                } => SourceKeyId,
            }
        }
        pub fn KeyId(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
                ReEncryptResponse::ReEncryptResponse {
                    CiphertextBlob,
                    SourceKeyId,
                    KeyId,
                    SourceEncryptionAlgorithm,
                    DestinationEncryptionAlgorithm,
                } => KeyId,
            }
        }
        pub fn SourceEncryptionAlgorithm(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>>{
            match self {
                ReEncryptResponse::ReEncryptResponse {
                    CiphertextBlob,
                    SourceKeyId,
                    KeyId,
                    SourceEncryptionAlgorithm,
                    DestinationEncryptionAlgorithm,
                } => SourceEncryptionAlgorithm,
            }
        }
        pub fn DestinationEncryptionAlgorithm(&self) -> &::std::rc::Rc<super::r#_Wrappers_Compile::Option<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptionAlgorithmSpec>>>{
            match self {
                ReEncryptResponse::ReEncryptResponse {
                    CiphertextBlob,
                    SourceKeyId,
                    KeyId,
                    SourceEncryptionAlgorithm,
                    DestinationEncryptionAlgorithm,
                } => DestinationEncryptionAlgorithm,
            }
        }
    }

    impl ::std::fmt::Debug for ReEncryptResponse {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for ReEncryptResponse {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                ReEncryptResponse::ReEncryptResponse {
                    CiphertextBlob,
                    SourceKeyId,
                    KeyId,
                    SourceEncryptionAlgorithm,
                    DestinationEncryptionAlgorithm,
                } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.ReEncryptResponse.ReEncryptResponse(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(CiphertextBlob, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(SourceKeyId, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(KeyId, _formatter, false)?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(
                        SourceEncryptionAlgorithm,
                        _formatter,
                        false,
                    )?;
                    write!(_formatter, ", ")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(
                        DestinationEncryptionAlgorithm,
                        _formatter,
                        false,
                    )?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for ReEncryptResponse {}

    impl ::std::hash::Hash for ReEncryptResponse {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                ReEncryptResponse::ReEncryptResponse {
                    CiphertextBlob,
                    SourceKeyId,
                    KeyId,
                    SourceEncryptionAlgorithm,
                    DestinationEncryptionAlgorithm,
                } => {
                    CiphertextBlob.hash(_state);
                    SourceKeyId.hash(_state);
                    KeyId.hash(_state);
                    SourceEncryptionAlgorithm.hash(_state);
                    DestinationEncryptionAlgorithm.hash(_state)
                }
            }
        }
    }

    impl ::std::default::Default for ReEncryptResponse {
        fn default() -> ReEncryptResponse {
            ReEncryptResponse::ReEncryptResponse {
                CiphertextBlob: ::std::default::Default::default(),
                SourceKeyId: ::std::default::Default::default(),
                KeyId: ::std::default::Default::default(),
                SourceEncryptionAlgorithm: ::std::default::Default::default(),
                DestinationEncryptionAlgorithm: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<ReEncryptResponse> for &ReEncryptResponse {
        fn as_ref(&self) -> Self {
            self
        }
    }

    #[derive(PartialEq, Clone)]
    pub enum SigningAlgorithmSpec {
        RSASSA_PSS_SHA_256 {},
        RSASSA_PSS_SHA_384 {},
        RSASSA_PSS_SHA_512 {},
        RSASSA_PKCS1_V1_5_SHA_256 {},
        RSASSA_PKCS1_V1_5_SHA_384 {},
        RSASSA_PKCS1_V1_5_SHA_512 {},
        ECDSA_SHA_256 {},
        ECDSA_SHA_384 {},
        ECDSA_SHA_512 {},
        SM2DSA {},
    }

    impl SigningAlgorithmSpec {}

    impl ::std::fmt::Debug for SigningAlgorithmSpec {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for SigningAlgorithmSpec {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                SigningAlgorithmSpec::RSASSA_PSS_SHA_256 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.RSASSA__PSS__SHA__256")?;
                    Ok(())
                }
                SigningAlgorithmSpec::RSASSA_PSS_SHA_384 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.RSASSA__PSS__SHA__384")?;
                    Ok(())
                }
                SigningAlgorithmSpec::RSASSA_PSS_SHA_512 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.RSASSA__PSS__SHA__512")?;
                    Ok(())
                }
                SigningAlgorithmSpec::RSASSA_PKCS1_V1_5_SHA_256 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.RSASSA__PKCS1__V1__5__SHA__256")?;
                    Ok(())
                }
                SigningAlgorithmSpec::RSASSA_PKCS1_V1_5_SHA_384 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.RSASSA__PKCS1__V1__5__SHA__384")?;
                    Ok(())
                }
                SigningAlgorithmSpec::RSASSA_PKCS1_V1_5_SHA_512 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.RSASSA__PKCS1__V1__5__SHA__512")?;
                    Ok(())
                }
                SigningAlgorithmSpec::ECDSA_SHA_256 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.ECDSA__SHA__256")?;
                    Ok(())
                }
                SigningAlgorithmSpec::ECDSA_SHA_384 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.ECDSA__SHA__384")?;
                    Ok(())
                }
                SigningAlgorithmSpec::ECDSA_SHA_512 {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.ECDSA__SHA__512")?;
                    Ok(())
                }
                SigningAlgorithmSpec::SM2DSA {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.SigningAlgorithmSpec.SM2DSA")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for SigningAlgorithmSpec {}

    impl ::std::hash::Hash for SigningAlgorithmSpec {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                SigningAlgorithmSpec::RSASSA_PSS_SHA_256 {} => {}
                SigningAlgorithmSpec::RSASSA_PSS_SHA_384 {} => {}
                SigningAlgorithmSpec::RSASSA_PSS_SHA_512 {} => {}
                SigningAlgorithmSpec::RSASSA_PKCS1_V1_5_SHA_256 {} => {}
                SigningAlgorithmSpec::RSASSA_PKCS1_V1_5_SHA_384 {} => {}
                SigningAlgorithmSpec::RSASSA_PKCS1_V1_5_SHA_512 {} => {}
                SigningAlgorithmSpec::ECDSA_SHA_256 {} => {}
                SigningAlgorithmSpec::ECDSA_SHA_384 {} => {}
                SigningAlgorithmSpec::ECDSA_SHA_512 {} => {}
                SigningAlgorithmSpec::SM2DSA {} => {}
            }
        }
    }

    impl ::std::default::Default for SigningAlgorithmSpec {
        fn default() -> SigningAlgorithmSpec {
            SigningAlgorithmSpec::RSASSA_PSS_SHA_256 {}
        }
    }

    impl ::std::convert::AsRef<SigningAlgorithmSpec> for &SigningAlgorithmSpec {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub struct IKMSClientCallHistory {}

    impl IKMSClientCallHistory {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn ::std::any::Any>
    for super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClientCallHistory {
    ::dafny_runtime::UpcastObjectFn!(dyn ::std::any::Any);
  }

    pub trait IKMSClient:
        ::std::any::Any + ::dafny_runtime::UpcastObject<dyn::std::any::Any>
    {
        fn Decrypt(&mut self, input: &::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DecryptRequest>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DecryptResponse>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>>;
        fn DeriveSharedSecret(&mut self, input: &::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DeriveSharedSecretRequest>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DeriveSharedSecretResponse>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>>;
        fn Encrypt(&mut self, input: &::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptRequest>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::EncryptResponse>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>>;
        fn GenerateDataKey(&mut self, input: &::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GenerateDataKeyRequest>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GenerateDataKeyResponse>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>>;
        fn GenerateDataKeyWithoutPlaintext(&mut self, input: &::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GenerateDataKeyWithoutPlaintextRequest>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GenerateDataKeyWithoutPlaintextResponse>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>>;
        fn GetPublicKey(&mut self, input: &::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GetPublicKeyRequest>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GetPublicKeyResponse>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>>;
        fn ReEncrypt(&mut self, input: &::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::ReEncryptRequest>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::ReEncryptResponse>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>>;
    }

    #[derive(PartialEq, Clone)]
    pub enum Error {
        DependencyTimeoutException {
            message: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
        DisabledException {
            message: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
        DryRunOperationException {
            message: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
        IncorrectKeyException {
            message: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
        InvalidArnException {
            message: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
        InvalidCiphertextException {
            message: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
        InvalidGrantTokenException {
            message: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
        InvalidKeyUsageException {
            message: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
        KeyUnavailableException {
            message: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
        KMSInternalException {
            message: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
        KMSInvalidStateException {
            message: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
        NotFoundException {
            message: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
        UnsupportedOperationException {
            message: ::std::rc::Rc<
                super::r#_Wrappers_Compile::Option<
                    ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
                >,
            >,
        },
        Opaque {
            obj: ::dafny_runtime::Object<dyn::std::any::Any>,
        },
    }

    impl Error {
        pub fn message(
            &self,
        ) -> &::std::rc::Rc<
            super::r#_Wrappers_Compile::Option<
                ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
            >,
        > {
            match self {
                Error::DependencyTimeoutException { message } => message,
                Error::DisabledException { message } => message,
                Error::DryRunOperationException { message } => message,
                Error::IncorrectKeyException { message } => message,
                Error::InvalidArnException { message } => message,
                Error::InvalidCiphertextException { message } => message,
                Error::InvalidGrantTokenException { message } => message,
                Error::InvalidKeyUsageException { message } => message,
                Error::KeyUnavailableException { message } => message,
                Error::KMSInternalException { message } => message,
                Error::KMSInvalidStateException { message } => message,
                Error::NotFoundException { message } => message,
                Error::UnsupportedOperationException { message } => message,
                Error::Opaque { obj } => panic!("field does not exist on this variant"),
            }
        }
        pub fn obj(&self) -> &::dafny_runtime::Object<dyn::std::any::Any> {
            match self {
                Error::DependencyTimeoutException { message } => {
                    panic!("field does not exist on this variant")
                }
                Error::DisabledException { message } => {
                    panic!("field does not exist on this variant")
                }
                Error::DryRunOperationException { message } => {
                    panic!("field does not exist on this variant")
                }
                Error::IncorrectKeyException { message } => {
                    panic!("field does not exist on this variant")
                }
                Error::InvalidArnException { message } => {
                    panic!("field does not exist on this variant")
                }
                Error::InvalidCiphertextException { message } => {
                    panic!("field does not exist on this variant")
                }
                Error::InvalidGrantTokenException { message } => {
                    panic!("field does not exist on this variant")
                }
                Error::InvalidKeyUsageException { message } => {
                    panic!("field does not exist on this variant")
                }
                Error::KeyUnavailableException { message } => {
                    panic!("field does not exist on this variant")
                }
                Error::KMSInternalException { message } => {
                    panic!("field does not exist on this variant")
                }
                Error::KMSInvalidStateException { message } => {
                    panic!("field does not exist on this variant")
                }
                Error::NotFoundException { message } => {
                    panic!("field does not exist on this variant")
                }
                Error::UnsupportedOperationException { message } => {
                    panic!("field does not exist on this variant")
                }
                Error::Opaque { obj } => obj,
            }
        }
    }

    impl ::std::fmt::Debug for Error {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for Error {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                Error::DependencyTimeoutException { message } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.DependencyTimeoutException(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                Error::DisabledException { message } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.DisabledException(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                Error::DryRunOperationException { message } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.DryRunOperationException(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                Error::IncorrectKeyException { message } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.IncorrectKeyException(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                Error::InvalidArnException { message } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.InvalidArnException(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                Error::InvalidCiphertextException { message } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.InvalidCiphertextException(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                Error::InvalidGrantTokenException { message } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.InvalidGrantTokenException(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                Error::InvalidKeyUsageException { message } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.InvalidKeyUsageException(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                Error::KeyUnavailableException { message } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.KeyUnavailableException(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                Error::KMSInternalException { message } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.KMSInternalException(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                Error::KMSInvalidStateException { message } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.KMSInvalidStateException(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                Error::NotFoundException { message } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.NotFoundException(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                Error::UnsupportedOperationException { message } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.UnsupportedOperationException(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(message, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
                Error::Opaque { obj } => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.types.Error.Opaque(")?;
                    ::dafny_runtime::DafnyPrint::fmt_print(obj, _formatter, false)?;
                    write!(_formatter, ")")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for Error {}

    impl ::std::hash::Hash for Error {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                Error::DependencyTimeoutException { message } => message.hash(_state),
                Error::DisabledException { message } => message.hash(_state),
                Error::DryRunOperationException { message } => message.hash(_state),
                Error::IncorrectKeyException { message } => message.hash(_state),
                Error::InvalidArnException { message } => message.hash(_state),
                Error::InvalidCiphertextException { message } => message.hash(_state),
                Error::InvalidGrantTokenException { message } => message.hash(_state),
                Error::InvalidKeyUsageException { message } => message.hash(_state),
                Error::KeyUnavailableException { message } => message.hash(_state),
                Error::KMSInternalException { message } => message.hash(_state),
                Error::KMSInvalidStateException { message } => message.hash(_state),
                Error::NotFoundException { message } => message.hash(_state),
                Error::UnsupportedOperationException { message } => message.hash(_state),
                Error::Opaque { obj } => obj.hash(_state),
            }
        }
    }

    impl ::std::default::Default for Error {
        fn default() -> Error {
            Error::DependencyTimeoutException {
                message: ::std::default::Default::default(),
            }
        }
    }

    impl ::std::convert::AsRef<Error> for &Error {
        fn as_ref(&self) -> Self {
            self
        }
    }

    pub type OpaqueError = ::std::rc::Rc<
        super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error,
    >;
}
pub mod r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny {
    pub struct _default {}

    impl _default {
        pub fn _allocate_object() -> ::dafny_runtime::Object<Self> {
            ::dafny_runtime::allocate_object::<Self>()
        }
        pub fn DefaultKMSClientConfigType() -> ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny::KMSClientConfigType>{
            ::std::rc::Rc::new(super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny::KMSClientConfigType::KMSClientConfigType {})
        }
        pub fn CreateSuccessOfClient(client: &::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>>{
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>::Success {
          value: client.clone()
        })
        }
        pub fn CreateFailureOfError(error: &::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>) -> ::std::rc::Rc<super::r#_Wrappers_Compile::Result<::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>>{
            ::std::rc::Rc::new(super::r#_Wrappers_Compile::Result::<::dafny_runtime::Object<dyn super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::IKMSClient>, ::std::rc::Rc<super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error>>::Failure {
          error: error.clone()
        })
        }
    }

    impl ::dafny_runtime::UpcastObject<dyn::std::any::Any>
        for super::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny::_default
    {
        ::dafny_runtime::UpcastObjectFn!(dyn::std::any::Any);
    }

    #[derive(PartialEq, Clone)]
    pub enum KMSClientConfigType {
        KMSClientConfigType {},
    }

    impl KMSClientConfigType {}

    impl ::std::fmt::Debug for KMSClientConfigType {
        fn fmt(&self, f: &mut ::std::fmt::Formatter) -> std::fmt::Result {
            ::dafny_runtime::DafnyPrint::fmt_print(self, f, true)
        }
    }

    impl ::dafny_runtime::DafnyPrint for KMSClientConfigType {
        fn fmt_print(
            &self,
            _formatter: &mut ::std::fmt::Formatter,
            _in_seq: bool,
        ) -> std::fmt::Result {
            match self {
                KMSClientConfigType::KMSClientConfigType {} => {
                    write!(_formatter, "software.amazon.cryptography.services.kms.internaldafny.KMSClientConfigType.KMSClientConfigType")?;
                    Ok(())
                }
            }
        }
    }

    impl Eq for KMSClientConfigType {}

    impl ::std::hash::Hash for KMSClientConfigType {
        fn hash<_H: ::std::hash::Hasher>(&self, _state: &mut _H) {
            match self {
                KMSClientConfigType::KMSClientConfigType {} => {}
            }
        }
    }

    impl ::std::default::Default for KMSClientConfigType {
        fn default() -> KMSClientConfigType {
            KMSClientConfigType::KMSClientConfigType {}
        }
    }

    impl ::std::convert::AsRef<KMSClientConfigType> for &KMSClientConfigType {
        fn as_ref(&self) -> Self {
            self
        }
    }
}
pub mod r#_Com_Compile_dAmazonaws_Compile {}
pub mod r#_Com_Compile {}
pub mod _module {}
