// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny_error(
    value: &::aws_smithy_runtime_api::client::result::SdkError<
        aws_sdk_kms::operation::create_key::CreateKeyError,
        ::aws_smithy_runtime_api::client::orchestrator::HttpResponse,
    >,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error> {
    match value {
      aws_sdk_kms::error::SdkError::ServiceError(service_error) => match service_error.err() {
                aws_sdk_kms::operation::create_key::CreateKeyError::CloudHsmClusterInvalidConfigurationException(e) =>
            crate::conversions::error::cloud_hsm_cluster_invalid_configuration_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::create_key::CreateKeyError::CustomKeyStoreInvalidStateException(e) =>
            crate::conversions::error::custom_key_store_invalid_state_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::create_key::CreateKeyError::CustomKeyStoreNotFoundException(e) =>
            crate::conversions::error::custom_key_store_not_found_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::create_key::CreateKeyError::DependencyTimeoutException(e) =>
            crate::conversions::error::dependency_timeout_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::create_key::CreateKeyError::InvalidArnException(e) =>
            crate::conversions::error::invalid_arn_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::create_key::CreateKeyError::KmsInternalException(e) =>
            crate::conversions::error::kms_internal_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::create_key::CreateKeyError::LimitExceededException(e) =>
            crate::conversions::error::limit_exceeded_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::create_key::CreateKeyError::MalformedPolicyDocumentException(e) =>
            crate::conversions::error::malformed_policy_document_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::create_key::CreateKeyError::TagException(e) =>
            crate::conversions::error::tag_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::create_key::CreateKeyError::UnsupportedOperationException(e) =>
            crate::conversions::error::unsupported_operation_exception::to_dafny(e.clone()),
        e => crate::conversions::error::to_opaque_error(e.to_string()),
      },
      _ => {
        crate::conversions::error::to_opaque_error(value.to_string())
      }
   }
}

 pub mod _create_key_request;

 pub mod _create_key_response;
