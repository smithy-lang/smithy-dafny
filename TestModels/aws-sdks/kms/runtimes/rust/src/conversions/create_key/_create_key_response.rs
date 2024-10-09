// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_kms::operation::create_key::CreateKeyOutput
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::services::kms::internaldafny::types::CreateKeyResponse,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::kms::internaldafny::types::CreateKeyResponse::CreateKeyResponse {
        KeyMetadata: ::std::rc::Rc::new(match &value.key_metadata {
    Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::conversions::key_metadata::to_dafny(x) },
    None => crate::_Wrappers_Compile::Option::None { }
})
,
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::kms::internaldafny::types::CreateKeyResponse,
    >
) -> aws_sdk_kms::operation::create_key::CreateKeyOutput {
    aws_sdk_kms::operation::create_key::CreateKeyOutput::builder()
          .set_key_metadata(match (*dafny_value.KeyMetadata()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(crate::conversions::key_metadata::from_dafny(value.clone())),
    _ => None,
}
)
          .build()


}
