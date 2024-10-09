// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny_error(
    value: &::aws_smithy_runtime_api::client::result::SdkError<
        aws_sdk_kms::operation::describe_custom_key_stores::DescribeCustomKeyStoresError,
        ::aws_smithy_runtime_api::client::orchestrator::HttpResponse,
    >,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::Error> {
    match value {
      aws_sdk_kms::error::SdkError::ServiceError(service_error) => match service_error.err() {
                aws_sdk_kms::operation::describe_custom_key_stores::DescribeCustomKeyStoresError::CustomKeyStoreNotFoundException(e) =>
            crate::conversions::error::custom_key_store_not_found_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::describe_custom_key_stores::DescribeCustomKeyStoresError::InvalidMarkerException(e) =>
            crate::conversions::error::invalid_marker_exception::to_dafny(e.clone()),
         aws_sdk_kms::operation::describe_custom_key_stores::DescribeCustomKeyStoresError::KmsInternalException(e) =>
            crate::conversions::error::kms_internal_exception::to_dafny(e.clone()),
        e => crate::conversions::error::to_opaque_error(e.to_string()),
      },
      _ => {
        crate::conversions::error::to_opaque_error(value.to_string())
      }
   }
}

 pub mod _describe_custom_key_stores_request;

 pub mod _describe_custom_key_stores_response;
