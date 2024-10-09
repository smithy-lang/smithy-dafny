// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny_error(
    value: &::aws_smithy_runtime_api::client::result::SdkError<
        aws_sdk_kms::operation::put_key_policy::PutKeyPolicyError,
        ::aws_smithy_runtime_api::client::orchestrator::HttpResponse,
    >,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error> {
    match value {
      aws_sdk_kms::error::SdkError::ServiceError(service_error) => match service_error.err() {
                aws_sdk_kms::operation::put_key_policy::PutKeyPolicyError::DependencyTimeoutException(e) =>
            crate::conversions::error::dependency_timeout_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::put_key_policy::PutKeyPolicyError::InvalidArnException(e) =>
            crate::conversions::error::invalid_arn_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::put_key_policy::PutKeyPolicyError::KmsInternalException(e) =>
            crate::conversions::error::kms_internal_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::put_key_policy::PutKeyPolicyError::KmsInvalidStateException(e) =>
            crate::conversions::error::kms_invalid_state_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::put_key_policy::PutKeyPolicyError::LimitExceededException(e) =>
            crate::conversions::error::limit_exceeded_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::put_key_policy::PutKeyPolicyError::MalformedPolicyDocumentException(e) =>
            crate::conversions::error::malformed_policy_document_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::put_key_policy::PutKeyPolicyError::NotFoundException(e) =>
            crate::conversions::error::not_found_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::put_key_policy::PutKeyPolicyError::UnsupportedOperationException(e) =>
            crate::conversions::error::unsupported_operation_exception::to_dafny(e.clone()),
        e => crate::conversions::error::to_opaque_error(e.to_string()),
      },
      _ => {
        crate::conversions::error::to_opaque_error(value.to_string())
      }
   }
}

 pub mod _put_key_policy_request;
