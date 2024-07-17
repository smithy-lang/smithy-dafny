// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_kms::operation::derive_shared_secret::DeriveSharedSecretOutput
) -> ::std::rc::Rc<
    crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DeriveSharedSecretResponse,
>{
    ::std::rc::Rc::new(crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DeriveSharedSecretResponse::DeriveSharedSecretResponse {
        KeyId: dafny_standard_library::conversion::ostring_to_dafny(&value.key_id),
 SharedSecret: dafny_standard_library::conversion::oblob_to_dafny(&value.shared_secret),
 CiphertextForRecipient: dafny_standard_library::conversion::oblob_to_dafny(&value.ciphertext_for_recipient),
 KeyAgreementAlgorithm: ::std::rc::Rc::new(match &value.key_agreement_algorithm {
    Some(x) => crate::implementation_from_dafny::_Wrappers_Compile::Option::Some { value: crate::conversions::key_agreement_algorithm_spec::to_dafny(x.clone()) },
    None => crate::implementation_from_dafny::_Wrappers_Compile::Option::None { }
})
,
 KeyOrigin: ::std::rc::Rc::new(match &value.key_origin {
    Some(x) => crate::implementation_from_dafny::_Wrappers_Compile::Option::Some { value: crate::conversions::origin_type::to_dafny(x.clone()) },
    None => crate::implementation_from_dafny::_Wrappers_Compile::Option::None { }
})
,
    })
}
