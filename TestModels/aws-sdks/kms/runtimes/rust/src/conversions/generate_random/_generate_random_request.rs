// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_kms::operation::generate_random::GenerateRandomInput,
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GenerateRandomRequest,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GenerateRandomRequest::GenerateRandomRequest {
        NumberOfBytes: crate::standard_library_conversions::oint_to_dafny(value.number_of_bytes),
 CustomKeyStoreId: crate::standard_library_conversions::ostring_to_dafny(&value.custom_key_store_id),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GenerateRandomRequest,
    >
) -> aws_sdk_kms::operation::generate_random::GenerateRandomInput {
    aws_sdk_kms::operation::generate_random::GenerateRandomInput::builder()
          .set_number_of_bytes(crate::standard_library_conversions::oint_from_dafny(dafny_value.NumberOfBytes().clone()))
 .set_custom_key_store_id(crate::standard_library_conversions::ostring_from_dafny(dafny_value.CustomKeyStoreId().clone()))
          .build()
          .unwrap()
}
