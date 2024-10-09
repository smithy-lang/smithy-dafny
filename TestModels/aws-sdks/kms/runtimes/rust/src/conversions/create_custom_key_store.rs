// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny_error(
    value: &::aws_smithy_runtime_api::client::result::SdkError<
        aws_sdk_kms::operation::create_custom_key_store::CreateCustomKeyStoreError,
        ::aws_smithy_runtime_api::client::orchestrator::HttpResponse,
    >,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error> {
    match value {
      aws_sdk_kms::error::SdkError::ServiceError(service_error) => match service_error.err() {
                aws_sdk_kms::operation::create_custom_key_store::CreateCustomKeyStoreError::CloudHsmClusterInUseException(e) =>
            crate::conversions::error::cloud_hsm_cluster_in_use_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::create_custom_key_store::CreateCustomKeyStoreError::CloudHsmClusterInvalidConfigurationException(e) =>
            crate::conversions::error::cloud_hsm_cluster_invalid_configuration_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::create_custom_key_store::CreateCustomKeyStoreError::CloudHsmClusterNotActiveException(e) =>
            crate::conversions::error::cloud_hsm_cluster_not_active_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::create_custom_key_store::CreateCustomKeyStoreError::CloudHsmClusterNotFoundException(e) =>
            crate::conversions::error::cloud_hsm_cluster_not_found_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::create_custom_key_store::CreateCustomKeyStoreError::CustomKeyStoreNameInUseException(e) =>
            crate::conversions::error::custom_key_store_name_in_use_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::create_custom_key_store::CreateCustomKeyStoreError::IncorrectTrustAnchorException(e) =>
            crate::conversions::error::incorrect_trust_anchor_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::create_custom_key_store::CreateCustomKeyStoreError::KmsInternalException(e) =>
            crate::conversions::error::kms_internal_exception::to_dafny(e.clone()),
        e => crate::conversions::error::to_opaque_error(e.to_string()),
      },
      _ => {
        crate::conversions::error::to_opaque_error(value.to_string())
      }
   }
}

 pub mod _create_custom_key_store_request;

 pub mod _create_custom_key_store_response;
