// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub mod dependency_timeout_exception;

 pub mod disabled_exception;

 pub mod dry_run_operation_exception;

 pub mod incorrect_key_exception;

 pub mod invalid_arn_exception;

 pub mod invalid_ciphertext_exception;

 pub mod invalid_grant_token_exception;

 pub mod invalid_key_usage_exception;

 pub mod key_unavailable_exception;

 pub mod kms_internal_exception;

 pub mod kms_invalid_state_exception;

 pub mod not_found_exception;

 pub mod unsupported_operation_exception;
 /// Wraps up an arbitrary Rust Error value as a Dafny Error
pub fn to_opaque_error<E: 'static>(value: E) ->
    ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
{
    let error_obj: ::dafny_runtime::Object<dyn::std::any::Any> = ::dafny_runtime::Object(Some(
        ::std::rc::Rc::new(::std::cell::UnsafeCell::new(value)),
    ));
    ::std::rc::Rc::new(
        crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::Opaque {
            obj: error_obj,
        },
    )
}

/// Wraps up an arbitrary Rust Error value as a Dafny Result<T, Error>.Failure
pub fn to_opaque_error_result<T: ::dafny_runtime::DafnyType, E: 'static>(value: E) ->
    ::std::rc::Rc<
        crate::_Wrappers_Compile::Result<
            T,
            ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error>
        >
    >
{
    ::std::rc::Rc::new(crate::_Wrappers_Compile::Result::Failure {
        error: to_opaque_error(value),
    })
}
pub fn to_dafny(
    value: crate::types::error::Error,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error> {
    match value {
        crate::types::error::Error::KmsInvalidStateException { error } =>
    crate::conversions::error::kms_invalid_state_exception::to_dafny(error),
crate::types::error::Error::KmsInternalException { error } =>
    crate::conversions::error::kms_internal_exception::to_dafny(error),
crate::types::error::Error::InvalidArnException { error } =>
    crate::conversions::error::invalid_arn_exception::to_dafny(error),
crate::types::error::Error::NotFoundException { error } =>
    crate::conversions::error::not_found_exception::to_dafny(error),
crate::types::error::Error::DisabledException { error } =>
    crate::conversions::error::disabled_exception::to_dafny(error),
crate::types::error::Error::IncorrectKeyException { error } =>
    crate::conversions::error::incorrect_key_exception::to_dafny(error),
crate::types::error::Error::DependencyTimeoutException { error } =>
    crate::conversions::error::dependency_timeout_exception::to_dafny(error),
crate::types::error::Error::InvalidCiphertextException { error } =>
    crate::conversions::error::invalid_ciphertext_exception::to_dafny(error),
crate::types::error::Error::UnsupportedOperationException { error } =>
    crate::conversions::error::unsupported_operation_exception::to_dafny(error),
crate::types::error::Error::DryRunOperationException { error } =>
    crate::conversions::error::dry_run_operation_exception::to_dafny(error),
crate::types::error::Error::KeyUnavailableException { error } =>
    crate::conversions::error::key_unavailable_exception::to_dafny(error),
crate::types::error::Error::InvalidKeyUsageException { error } =>
    crate::conversions::error::invalid_key_usage_exception::to_dafny(error),
crate::types::error::Error::InvalidGrantTokenException { error } =>
    crate::conversions::error::invalid_grant_token_exception::to_dafny(error),
        crate::types::error::Error::Opaque { obj } =>
            ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::Opaque {
                obj: ::dafny_runtime::Object(obj.0)
            }),
    }
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error,
    >,
) -> crate::types::error::Error {
    match ::std::borrow::Borrow::borrow(&dafny_value) {
        crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::KMSInvalidStateException { message, .. } =>
  crate::types::error::Error::KmsInvalidStateException {
    error: aws_sdk_kms::types::error::KmsInvalidStateException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::KMSInternalException { message, .. } =>
  crate::types::error::Error::KmsInternalException {
    error: aws_sdk_kms::types::error::KmsInternalException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::InvalidArnException { message, .. } =>
  crate::types::error::Error::InvalidArnException {
    error: aws_sdk_kms::types::error::InvalidArnException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::NotFoundException { message, .. } =>
  crate::types::error::Error::NotFoundException {
    error: aws_sdk_kms::types::error::NotFoundException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::DisabledException { message, .. } =>
  crate::types::error::Error::DisabledException {
    error: aws_sdk_kms::types::error::DisabledException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::IncorrectKeyException { message, .. } =>
  crate::types::error::Error::IncorrectKeyException {
    error: aws_sdk_kms::types::error::IncorrectKeyException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::DependencyTimeoutException { message, .. } =>
  crate::types::error::Error::DependencyTimeoutException {
    error: aws_sdk_kms::types::error::DependencyTimeoutException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::InvalidCiphertextException { message, .. } =>
  crate::types::error::Error::InvalidCiphertextException {
    error: aws_sdk_kms::types::error::InvalidCiphertextException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::UnsupportedOperationException { message, .. } =>
  crate::types::error::Error::UnsupportedOperationException {
    error: aws_sdk_kms::types::error::UnsupportedOperationException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::DryRunOperationException { message, .. } =>
  crate::types::error::Error::DryRunOperationException {
    error: aws_sdk_kms::types::error::DryRunOperationException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::KeyUnavailableException { message, .. } =>
  crate::types::error::Error::KeyUnavailableException {
    error: aws_sdk_kms::types::error::KeyUnavailableException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::InvalidKeyUsageException { message, .. } =>
  crate::types::error::Error::InvalidKeyUsageException {
    error: aws_sdk_kms::types::error::InvalidKeyUsageException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::InvalidGrantTokenException { message, .. } =>
  crate::types::error::Error::InvalidGrantTokenException {
    error: aws_sdk_kms::types::error::InvalidGrantTokenException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
        crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error::Opaque { obj } =>
            crate::types::error::Error::Opaque {
                obj: obj.clone()
            },
    }
}
