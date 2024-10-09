// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_kms::operation::get_key_rotation_status::GetKeyRotationStatusOutput
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GetKeyRotationStatusResponse,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GetKeyRotationStatusResponse::GetKeyRotationStatusResponse {
        KeyRotationEnabled: crate::standard_library_conversions::obool_to_dafny(&Some(value.key_rotation_enabled)),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::kms::internaldafny::types::GetKeyRotationStatusResponse,
    >
) -> aws_sdk_kms::operation::get_key_rotation_status::GetKeyRotationStatusOutput {
    aws_sdk_kms::operation::get_key_rotation_status::GetKeyRotationStatusOutput::builder()
          .set_key_rotation_enabled(crate::standard_library_conversions::obool_from_dafny(dafny_value.KeyRotationEnabled().clone()))
          .build()


}
