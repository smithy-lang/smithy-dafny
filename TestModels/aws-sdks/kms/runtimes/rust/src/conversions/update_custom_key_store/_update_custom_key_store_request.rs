// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_kms::operation::update_custom_key_store::UpdateCustomKeyStoreInput,
) -> ::std::rc::Rc<
    crate::r#software::amazon::cryptography::services::kms::internaldafny::types::UpdateCustomKeyStoreRequest,
>{
    ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::kms::internaldafny::types::UpdateCustomKeyStoreRequest::UpdateCustomKeyStoreRequest {
        CustomKeyStoreId: crate::standard_library_conversions::ostring_to_dafny(&value.custom_key_store_id) .Extract(),
 NewCustomKeyStoreName: crate::standard_library_conversions::ostring_to_dafny(&value.new_custom_key_store_name),
 KeyStorePassword: crate::standard_library_conversions::ostring_to_dafny(&value.key_store_password),
 CloudHsmClusterId: crate::standard_library_conversions::ostring_to_dafny(&value.cloud_hsm_cluster_id),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::kms::internaldafny::types::UpdateCustomKeyStoreRequest,
    >
) -> aws_sdk_kms::operation::update_custom_key_store::UpdateCustomKeyStoreInput {
    aws_sdk_kms::operation::update_custom_key_store::UpdateCustomKeyStoreInput::builder()
          .set_custom_key_store_id(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.CustomKeyStoreId()) ))
 .set_new_custom_key_store_name(crate::standard_library_conversions::ostring_from_dafny(dafny_value.NewCustomKeyStoreName().clone()))
 .set_key_store_password(crate::standard_library_conversions::ostring_from_dafny(dafny_value.KeyStorePassword().clone()))
 .set_cloud_hsm_cluster_id(crate::standard_library_conversions::ostring_from_dafny(dafny_value.CloudHsmClusterId().clone()))
          .build()
          .unwrap()
}
