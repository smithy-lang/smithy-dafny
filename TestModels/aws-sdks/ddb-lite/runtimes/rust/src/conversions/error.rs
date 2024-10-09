// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub mod conditional_check_failed_exception;

 pub mod duplicate_item_exception;

 pub mod idempotent_parameter_mismatch_exception;

 pub mod internal_server_error;

 pub mod invalid_endpoint_exception;

 pub mod item_collection_size_limit_exceeded_exception;

 pub mod limit_exceeded_exception;

 pub mod provisioned_throughput_exceeded_exception;

 pub mod request_limit_exceeded;

 pub mod resource_in_use_exception;

 pub mod resource_not_found_exception;

 pub mod transaction_canceled_exception;

 pub mod transaction_conflict_exception;

 pub mod transaction_in_progress_exception;
 /// Wraps up an arbitrary Rust Error value as a Dafny Error
pub fn to_opaque_error<E: 'static>(value: E) ->
    ::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>
{
    let error_obj: ::dafny_runtime::Object<dyn::std::any::Any> = ::dafny_runtime::Object(Some(
        ::std::rc::Rc::new(::std::cell::UnsafeCell::new(value)),
    ));
    ::std::rc::Rc::new(
        crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error::Opaque {
            obj: error_obj,
        },
    )
}

/// Wraps up an arbitrary Rust Error value as a Dafny Result<T, Error>.Failure
pub fn to_opaque_error_result<T: ::dafny_runtime::DafnyType, E: 'static>(value: E) ->
    ::std::rc::Rc<
        crate::_Wrappers_Compile::Result<
            T,
            ::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error>
        >
    >
{
    ::std::rc::Rc::new(crate::_Wrappers_Compile::Result::Failure {
        error: to_opaque_error(value),
    })
}
pub fn to_dafny(
    value: crate::types::error::Error,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error> {
    match value {
        crate::types::error::Error::DuplicateItemException { error } =>
    crate::conversions::error::duplicate_item_exception::to_dafny(error),
crate::types::error::Error::ConditionalCheckFailedException { error } =>
    crate::conversions::error::conditional_check_failed_exception::to_dafny(error),
crate::types::error::Error::InternalServerError { error } =>
    crate::conversions::error::internal_server_error::to_dafny(error),
crate::types::error::Error::ResourceInUseException { error } =>
    crate::conversions::error::resource_in_use_exception::to_dafny(error),
crate::types::error::Error::TransactionCanceledException { error } =>
    crate::conversions::error::transaction_canceled_exception::to_dafny(error),
crate::types::error::Error::ResourceNotFoundException { error } =>
    crate::conversions::error::resource_not_found_exception::to_dafny(error),
crate::types::error::Error::TransactionConflictException { error } =>
    crate::conversions::error::transaction_conflict_exception::to_dafny(error),
crate::types::error::Error::ItemCollectionSizeLimitExceededException { error } =>
    crate::conversions::error::item_collection_size_limit_exceeded_exception::to_dafny(error),
crate::types::error::Error::InvalidEndpointException { error } =>
    crate::conversions::error::invalid_endpoint_exception::to_dafny(error),
crate::types::error::Error::ProvisionedThroughputExceededException { error } =>
    crate::conversions::error::provisioned_throughput_exceeded_exception::to_dafny(error),
crate::types::error::Error::IdempotentParameterMismatchException { error } =>
    crate::conversions::error::idempotent_parameter_mismatch_exception::to_dafny(error),
crate::types::error::Error::RequestLimitExceeded { error } =>
    crate::conversions::error::request_limit_exceeded::to_dafny(error),
crate::types::error::Error::LimitExceededException { error } =>
    crate::conversions::error::limit_exceeded_exception::to_dafny(error),
crate::types::error::Error::TransactionInProgressException { error } =>
    crate::conversions::error::transaction_in_progress_exception::to_dafny(error),
        crate::types::error::Error::Opaque { obj } =>
            ::std::rc::Rc::new(crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error::Opaque {
                obj: ::dafny_runtime::Object(obj.0)
            }),
    }
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error,
    >,
) -> crate::types::error::Error {
    match ::std::borrow::Borrow::borrow(&dafny_value) {
        crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error::DuplicateItemException { message, .. } =>
  crate::types::error::Error::DuplicateItemException {
    error: aws_sdk_dynamodb::types::error::DuplicateItemException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error::ConditionalCheckFailedException { message, .. } =>
  crate::types::error::Error::ConditionalCheckFailedException {
    error: aws_sdk_dynamodb::types::error::ConditionalCheckFailedException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error::InternalServerError { message, .. } =>
  crate::types::error::Error::InternalServerError {
    error: aws_sdk_dynamodb::types::error::InternalServerError::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error::ResourceInUseException { message, .. } =>
  crate::types::error::Error::ResourceInUseException {
    error: aws_sdk_dynamodb::types::error::ResourceInUseException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error::TransactionCanceledException { Message, .. } =>
  crate::types::error::Error::TransactionCanceledException {
    error: aws_sdk_dynamodb::types::error::TransactionCanceledException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(Message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error::ResourceNotFoundException { message, .. } =>
  crate::types::error::Error::ResourceNotFoundException {
    error: aws_sdk_dynamodb::types::error::ResourceNotFoundException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error::TransactionConflictException { message, .. } =>
  crate::types::error::Error::TransactionConflictException {
    error: aws_sdk_dynamodb::types::error::TransactionConflictException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error::ItemCollectionSizeLimitExceededException { message, .. } =>
  crate::types::error::Error::ItemCollectionSizeLimitExceededException {
    error: aws_sdk_dynamodb::types::error::ItemCollectionSizeLimitExceededException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error::InvalidEndpointException { Message, .. } =>
  crate::types::error::Error::InvalidEndpointException {
    error: aws_sdk_dynamodb::types::error::InvalidEndpointException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(Message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error::ProvisionedThroughputExceededException { message, .. } =>
  crate::types::error::Error::ProvisionedThroughputExceededException {
    error: aws_sdk_dynamodb::types::error::ProvisionedThroughputExceededException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error::IdempotentParameterMismatchException { Message, .. } =>
  crate::types::error::Error::IdempotentParameterMismatchException {
    error: aws_sdk_dynamodb::types::error::IdempotentParameterMismatchException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(Message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error::RequestLimitExceeded { message, .. } =>
  crate::types::error::Error::RequestLimitExceeded {
    error: aws_sdk_dynamodb::types::error::RequestLimitExceeded::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error::LimitExceededException { message, .. } =>
  crate::types::error::Error::LimitExceededException {
    error: aws_sdk_dynamodb::types::error::LimitExceededException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(message.clone()))
      .build()
  },
crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error::TransactionInProgressException { Message, .. } =>
  crate::types::error::Error::TransactionInProgressException {
    error: aws_sdk_dynamodb::types::error::TransactionInProgressException::builder()
      .set_message(crate::standard_library_conversions::ostring_from_dafny(Message.clone()))
      .build()
  },
        crate::r#software::amazon::cryptography::services::dynamodb::internaldafny::types::Error::Opaque { obj } =>
            crate::types::error::Error::Opaque {
                obj: obj.clone()
            },
    }
}
