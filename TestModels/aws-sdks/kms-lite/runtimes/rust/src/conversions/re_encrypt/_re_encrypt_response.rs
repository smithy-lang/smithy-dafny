// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_kms::operation::re_encrypt::ReEncryptOutput
) -> ::std::rc::Rc<
    crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::ReEncryptResponse,
>{
    ::std::rc::Rc::new(crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::ReEncryptResponse::ReEncryptResponse {
        CiphertextBlob: dafny_standard_library::conversion::oblob_to_dafny(&value.ciphertext_blob),
 SourceKeyId: dafny_standard_library::conversion::ostring_to_dafny(&value.source_key_id),
 KeyId: dafny_standard_library::conversion::ostring_to_dafny(&value.key_id),
 SourceEncryptionAlgorithm: ::std::rc::Rc::new(match &value.source_encryption_algorithm {
    Some(x) => crate::implementation_from_dafny::_Wrappers_Compile::Option::Some { value: crate::conversions::encryption_algorithm_spec::to_dafny(x.clone()) },
    None => crate::implementation_from_dafny::_Wrappers_Compile::Option::None { }
})
,
 DestinationEncryptionAlgorithm: ::std::rc::Rc::new(match &value.destination_encryption_algorithm {
    Some(x) => crate::implementation_from_dafny::_Wrappers_Compile::Option::Some { value: crate::conversions::encryption_algorithm_spec::to_dafny(x.clone()) },
    None => crate::implementation_from_dafny::_Wrappers_Compile::Option::None { }
})
,
    })
}
