// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny_error(
    value: &::aws_smithy_runtime_api::client::result::SdkError<
        aws_sdk_kms::operation::create_alias::CreateAliasError,
        ::aws_smithy_runtime_api::client::orchestrator::HttpResponse,
    >,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error> {
    match value {
      aws_sdk_kms::error::SdkError::ServiceError(service_error) => match service_error.err() {
                aws_sdk_kms::operation::create_alias::CreateAliasError::AlreadyExistsException(e) =>
            crate::conversions::error::already_exists_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::create_alias::CreateAliasError::DependencyTimeoutException(e) =>
            crate::conversions::error::dependency_timeout_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::create_alias::CreateAliasError::InvalidAliasNameException(e) =>
            crate::conversions::error::invalid_alias_name_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::create_alias::CreateAliasError::KmsInternalException(e) =>
            crate::conversions::error::kms_internal_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::create_alias::CreateAliasError::KmsInvalidStateException(e) =>
            crate::conversions::error::kms_invalid_state_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::create_alias::CreateAliasError::LimitExceededException(e) =>
            crate::conversions::error::limit_exceeded_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::create_alias::CreateAliasError::NotFoundException(e) =>
            crate::conversions::error::not_found_exception::to_dafny(e.clone()),
        e => crate::conversions::error::to_opaque_error(e.to_string()),
      },
      _ => {
        crate::conversions::error::to_opaque_error(value.to_string())
      }
   }
}

 pub mod _create_alias_request;
