// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
pub mod _put_item_request;

 pub mod _put_item_response;
 #[allow(dead_code)]
pub fn to_dafny_error(
    value: &::aws_smithy_runtime_api::client::result::SdkError<
        aws_sdk_dynamodb::operation::put_item::PutItemError,
        ::aws_smithy_runtime_api::client::orchestrator::HttpResponse,
    >,
) -> ::std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_ddynamodb_dinternaldafny_dtypes::Error> {
    match value {
      aws_sdk_dynamodb::error::SdkError::ServiceError(service_error) => match service_error.err() {
                aws_sdk_dynamodb::operation::put_item::PutItemError::InternalServerError(e) =>
            crate::conversions::error::internal_server_error::to_dafny(e.clone()),
         aws_sdk_dynamodb::operation::put_item::PutItemError::InvalidEndpointException(e) =>
            crate::conversions::error::invalid_endpoint_exception::to_dafny(e.clone()),
         aws_sdk_dynamodb::operation::put_item::PutItemError::ResourceNotFoundException(e) =>
            crate::conversions::error::resource_not_found_exception::to_dafny(e.clone()),
         aws_sdk_dynamodb::operation::put_item::PutItemError::RequestLimitExceeded(e) =>
            crate::conversions::error::request_limit_exceeded::to_dafny(e.clone()),
         aws_sdk_dynamodb::operation::put_item::PutItemError::TransactionConflictException(e) =>
            crate::conversions::error::transaction_conflict_exception::to_dafny(e.clone()),
         aws_sdk_dynamodb::operation::put_item::PutItemError::ConditionalCheckFailedException(e) =>
            crate::conversions::error::conditional_check_failed_exception::to_dafny(e.clone()),
         aws_sdk_dynamodb::operation::put_item::PutItemError::ItemCollectionSizeLimitExceededException(e) =>
            crate::conversions::error::item_collection_size_limit_exceeded_exception::to_dafny(e.clone()),
         aws_sdk_dynamodb::operation::put_item::PutItemError::ProvisionedThroughputExceededException(e) =>
            crate::conversions::error::provisioned_throughput_exceeded_exception::to_dafny(e.clone()),
        e => crate::conversions::error::to_opaque_error(e.to_string()),
      },
      _ => {
        crate::conversions::error::to_opaque_error(value.to_string())
      }
   }
}
