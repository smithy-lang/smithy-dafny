// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny_error(
    value: &::aws_smithy_runtime_api::client::result::SdkError<
        aws_sdk_kms::operation::verify::VerifyError,
        ::aws_smithy_runtime_api::client::orchestrator::HttpResponse,
    >,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error> {
    match value {
      aws_sdk_kms::error::SdkError::ServiceError(service_error) => match service_error.err() {
                aws_sdk_kms::operation::verify::VerifyError::DependencyTimeoutException(e) =>
            crate::conversions::error::dependency_timeout_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::verify::VerifyError::DisabledException(e) =>
            crate::conversions::error::disabled_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::verify::VerifyError::InvalidGrantTokenException(e) =>
            crate::conversions::error::invalid_grant_token_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::verify::VerifyError::InvalidKeyUsageException(e) =>
            crate::conversions::error::invalid_key_usage_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::verify::VerifyError::KeyUnavailableException(e) =>
            crate::conversions::error::key_unavailable_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::verify::VerifyError::KmsInternalException(e) =>
            crate::conversions::error::kms_internal_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::verify::VerifyError::KmsInvalidSignatureException(e) =>
            crate::conversions::error::kms_invalid_signature_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::verify::VerifyError::KmsInvalidStateException(e) =>
            crate::conversions::error::kms_invalid_state_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::verify::VerifyError::NotFoundException(e) =>
            crate::conversions::error::not_found_exception::to_dafny(e.clone()),
        e => crate::conversions::error::to_opaque_error(e.to_string()),
      },
      _ => {
        crate::conversions::error::to_opaque_error(value.to_string())
      }
   }
}

 pub mod _verify_request;

 pub mod _verify_response;
