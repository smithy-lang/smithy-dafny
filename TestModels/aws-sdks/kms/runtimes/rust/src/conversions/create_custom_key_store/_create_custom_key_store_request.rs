// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_kms::operation::create_custom_key_store::CreateCustomKeyStoreInput,
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::services::kms::internaldafny::types::CreateCustomKeyStoreRequest,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::kms::internaldafny::types::CreateCustomKeyStoreRequest::CreateCustomKeyStoreRequest {
        CustomKeyStoreName: crate::standard_library_conversions::ostring_to_dafny(&value.custom_key_store_name) .Extract(),
 CloudHsmClusterId: crate::standard_library_conversions::ostring_to_dafny(&value.cloud_hsm_cluster_id) .Extract(),
 TrustAnchorCertificate: crate::standard_library_conversions::ostring_to_dafny(&value.trust_anchor_certificate) .Extract(),
 KeyStorePassword: crate::standard_library_conversions::ostring_to_dafny(&value.key_store_password) .Extract(),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::kms::internaldafny::types::CreateCustomKeyStoreRequest,
    >
) -> aws_sdk_kms::operation::create_custom_key_store::CreateCustomKeyStoreInput {
    aws_sdk_kms::operation::create_custom_key_store::CreateCustomKeyStoreInput::builder()
          .set_custom_key_store_name(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.CustomKeyStoreName()) ))
 .set_cloud_hsm_cluster_id(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.CloudHsmClusterId()) ))
 .set_trust_anchor_certificate(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.TrustAnchorCertificate()) ))
 .set_key_store_password(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.KeyStorePassword()) ))
          .build()
          .unwrap()
}
