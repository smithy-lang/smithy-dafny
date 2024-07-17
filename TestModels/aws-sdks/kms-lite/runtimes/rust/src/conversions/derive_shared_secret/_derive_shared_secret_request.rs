// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_kms::operation::derive_shared_secret::DeriveSharedSecretRequest
) -> ::std::rc::Rc<
    crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DeriveSharedSecretRequest,
>{
    ::std::rc::Rc::new(crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DeriveSharedSecretRequest::DeriveSharedSecretRequest {
        KeyId: dafny_standard_library::conversion::ostring_to_dafny(&value.key_id) .Extract(),
 KeyAgreementAlgorithm: ::std::rc::Rc::new(match &value.key_agreement_algorithm {
    Some(x) => crate::implementation_from_dafny::_Wrappers_Compile::Option::Some { value: crate::conversions::key_agreement_algorithm_spec::to_dafny(x.clone()) },
    None => crate::implementation_from_dafny::_Wrappers_Compile::Option::None { }
})
,
 PublicKey: dafny_standard_library::conversion::oblob_to_dafny(&value.public_key),
 GrantTokens: ::std::rc::Rc::new(match &value.grant_tokens {
    Some(x) => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value :
        ::dafny_runtime::dafny_runtime_conversions::vec_to_dafny_sequence(x,
            |e| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(e),
        )
    },
    None => crate::implementation_from_dafny::r#_Wrappers_Compile::Option::None {}
})
,
 DryRun: dafny_standard_library::conversion::obool_to_dafny(&value.dry_run),
 Recipient: ::std::rc::Rc::new(match &value.recipient {
    Some(x) => crate::implementation_from_dafny::_Wrappers_Compile::Option::Some { value: crate::conversions::recipient_info::to_dafny(&x) },
    None => crate::implementation_from_dafny::_Wrappers_Compile::Option::None { }
})
,
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DeriveSharedSecretRequest,
    >,
    client: aws_sdk_kms::Client,
) -> aws_sdk_kms::operation::derive_shared_secret::builders::DeriveSharedSecretFluentBuilder {
    client.derive_shared_secret()
          .set_key_id(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.KeyId()) ))
 .set_key_agreement_algorithm(Some( crate::conversions::key_agreement_algorithm_spec::from_dafny(dafny_value.KeyAgreementAlgorithm()) ))
 .set_public_key(dafny_standard_library::conversion::oblob_from_dafny(dafny_value.PublicKey().clone()))
 .set_grant_tokens(match (*dafny_value.GrantTokens()).as_ref() {
    crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value } =>
        Some(
            ::dafny_runtime::dafny_runtime_conversions::dafny_sequence_to_vec(value,
                |e| dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(e),
            )
        ),
    _ => None
}
)
 .set_dry_run(dafny_standard_library::conversion::obool_from_dafny(dafny_value.DryRun().clone()))
 .set_recipient(match (*dafny_value.Recipient()).as_ref() {
    crate::implementation_from_dafny::r#_Wrappers_Compile::Option::Some { value } =>
        Some(crate::conversions::recipient_info::from_dafny(value.clone())),
    _ => None,
}
)
}
