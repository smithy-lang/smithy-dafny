// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &aws_sdk_kms::types::CustomKeyStoresListEntry,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::CustomKeyStoresListEntry>{
  ::std::rc::Rc::new(
    crate::r#software::amazon::cryptography::services::kms::internaldafny::types::CustomKeyStoresListEntry::CustomKeyStoresListEntry {
        CustomKeyStoreId: crate::standard_library_conversions::ostring_to_dafny(&value.custom_key_store_id),
 CustomKeyStoreName: crate::standard_library_conversions::ostring_to_dafny(&value.custom_key_store_name),
 CloudHsmClusterId: crate::standard_library_conversions::ostring_to_dafny(&value.cloud_hsm_cluster_id),
 TrustAnchorCertificate: crate::standard_library_conversions::ostring_to_dafny(&value.trust_anchor_certificate),
 ConnectionState: ::std::rc::Rc::new(match &value.connection_state {
    Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::conversions::connection_state_type::to_dafny(x.clone()) },
    None => crate::_Wrappers_Compile::Option::None { }
})
,
 ConnectionErrorCode: ::std::rc::Rc::new(match &value.connection_error_code {
    Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::conversions::connection_error_code_type::to_dafny(x.clone()) },
    None => crate::_Wrappers_Compile::Option::None { }
})
,
 CreationDate: crate::standard_library_conversions::otimestamp_to_dafny(&value.creation_date),
    }
  )
} #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::kms::internaldafny::types::CustomKeyStoresListEntry,
    >,
) -> aws_sdk_kms::types::CustomKeyStoresListEntry {
    aws_sdk_kms::types::CustomKeyStoresListEntry::builder()
          .set_custom_key_store_id(crate::standard_library_conversions::ostring_from_dafny(dafny_value.CustomKeyStoreId().clone()))
 .set_custom_key_store_name(crate::standard_library_conversions::ostring_from_dafny(dafny_value.CustomKeyStoreName().clone()))
 .set_cloud_hsm_cluster_id(crate::standard_library_conversions::ostring_from_dafny(dafny_value.CloudHsmClusterId().clone()))
 .set_trust_anchor_certificate(crate::standard_library_conversions::ostring_from_dafny(dafny_value.TrustAnchorCertificate().clone()))
 .set_connection_state(match &**dafny_value.ConnectionState() {
    crate::r#_Wrappers_Compile::Option::Some { value } => Some(
        crate::conversions::connection_state_type::from_dafny(value)
    ),
    _ => None,
}
)
 .set_connection_error_code(match &**dafny_value.ConnectionErrorCode() {
    crate::r#_Wrappers_Compile::Option::Some { value } => Some(
        crate::conversions::connection_error_code_type::from_dafny(value)
    ),
    _ => None,
}
)
 .set_creation_date(crate::standard_library_conversions::otimestamp_from_dafny(dafny_value.CreationDate().clone()))
          .build()

}
