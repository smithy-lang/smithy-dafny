// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_kms::operation::decrypt::DecryptOutput,
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DecryptResponse,
> {
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::kms::internaldafny::types::DecryptResponse::DecryptResponse {
        KeyId: crate::standard_library_conversions::ostring_to_dafny(&value.key_id),
 Plaintext: crate::standard_library_conversions::oblob_to_dafny(&value.plaintext),
 EncryptionAlgorithm: ::std::rc::Rc::new(match &value.encryption_algorithm {
    Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::conversions::encryption_algorithm_spec::to_dafny(x.clone()) },
    None => crate::_Wrappers_Compile::Option::None { }
})
,
 CiphertextForRecipient: crate::standard_library_conversions::oblob_to_dafny(&value.ciphertext_for_recipient),
    })
}
