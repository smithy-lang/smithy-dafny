// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny_error(
    value: &::aws_smithy_runtime_api::client::result::SdkError<
        aws_sdk_kms::operation::update_custom_key_store::UpdateCustomKeyStoreError,
        ::aws_smithy_runtime_api::client::orchestrator::HttpResponse,
    >,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error> {
    match value {
      aws_sdk_kms::error::SdkError::ServiceError(service_error) => match service_error.err() {
                aws_sdk_kms::operation::update_custom_key_store::UpdateCustomKeyStoreError::CloudHsmClusterInvalidConfigurationException(e) =>
            crate::conversions::error::cloud_hsm_cluster_invalid_configuration_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::update_custom_key_store::UpdateCustomKeyStoreError::CloudHsmClusterNotActiveException(e) =>
            crate::conversions::error::cloud_hsm_cluster_not_active_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::update_custom_key_store::UpdateCustomKeyStoreError::CloudHsmClusterNotFoundException(e) =>
            crate::conversions::error::cloud_hsm_cluster_not_found_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::update_custom_key_store::UpdateCustomKeyStoreError::CloudHsmClusterNotRelatedException(e) =>
            crate::conversions::error::cloud_hsm_cluster_not_related_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::update_custom_key_store::UpdateCustomKeyStoreError::CustomKeyStoreInvalidStateException(e) =>
            crate::conversions::error::custom_key_store_invalid_state_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::update_custom_key_store::UpdateCustomKeyStoreError::CustomKeyStoreNameInUseException(e) =>
            crate::conversions::error::custom_key_store_name_in_use_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::update_custom_key_store::UpdateCustomKeyStoreError::CustomKeyStoreNotFoundException(e) =>
            crate::conversions::error::custom_key_store_not_found_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::update_custom_key_store::UpdateCustomKeyStoreError::KmsInternalException(e) =>
            crate::conversions::error::kms_internal_exception::to_dafny(e.clone()),
        e => crate::conversions::error::to_opaque_error(e.to_string()),
      },
      _ => {
        crate::conversions::error::to_opaque_error(value.to_string())
      }
   }
}

 pub mod _update_custom_key_store_request;

 pub mod _update_custom_key_store_response;
