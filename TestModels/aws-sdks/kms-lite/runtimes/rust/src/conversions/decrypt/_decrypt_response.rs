// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_kms::operation::decrypt::DecryptOutput
) -> ::std::rc::Rc<
    crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DecryptResponse,
>{
    ::std::rc::Rc::new(crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::DecryptResponse::DecryptResponse {
        KeyId: dafny_standard_library::conversion::ostring_to_dafny(&value.key_id),
 Plaintext: dafny_standard_library::conversion::oblob_to_dafny(&value.plaintext),
 EncryptionAlgorithm: ::std::rc::Rc::new(match &value.encryption_algorithm {
    Some(x) => crate::implementation_from_dafny::_Wrappers_Compile::Option::Some { value: crate::conversions::encryption_algorithm_spec::to_dafny(x.clone()) },
    None => crate::implementation_from_dafny::_Wrappers_Compile::Option::None { }
})
,
 CiphertextForRecipient: dafny_standard_library::conversion::oblob_to_dafny(&value.ciphertext_for_recipient),
    })
}
