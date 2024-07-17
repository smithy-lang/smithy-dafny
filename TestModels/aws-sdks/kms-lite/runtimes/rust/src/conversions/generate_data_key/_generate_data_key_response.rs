// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_kms::operation::generate_data_key::GenerateDataKeyResponse
) -> ::std::rc::Rc<
    crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GenerateDataKeyResponse,
>{
    ::std::rc::Rc::new(crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::GenerateDataKeyResponse::GenerateDataKeyResponse {
        CiphertextBlob: dafny_standard_library::conversion::oblob_to_dafny(&value.ciphertext_blob),
 Plaintext: dafny_standard_library::conversion::oblob_to_dafny(&value.plaintext),
 KeyId: dafny_standard_library::conversion::ostring_to_dafny(&value.key_id),
 CiphertextForRecipient: dafny_standard_library::conversion::oblob_to_dafny(&value.ciphertext_for_recipient),
    })
}
