// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[derive(::std::clone::Clone, ::std::fmt::Debug, ::std::cmp::PartialEq)]
pub enum Error {
    DuplicateItemException {
    error: aws_sdk_dynamodb::types::error::DuplicateItemException,
},

ConditionalCheckFailedException {
    error: aws_sdk_dynamodb::types::error::ConditionalCheckFailedException,
},

InternalServerError {
    error: aws_sdk_dynamodb::types::error::InternalServerError,
},

ResourceInUseException {
    error: aws_sdk_dynamodb::types::error::ResourceInUseException,
},

TransactionCanceledException {
    error: aws_sdk_dynamodb::types::error::TransactionCanceledException,
},

ResourceNotFoundException {
    error: aws_sdk_dynamodb::types::error::ResourceNotFoundException,
},

TransactionConflictException {
    error: aws_sdk_dynamodb::types::error::TransactionConflictException,
},

ItemCollectionSizeLimitExceededException {
    error: aws_sdk_dynamodb::types::error::ItemCollectionSizeLimitExceededException,
},

InvalidEndpointException {
    error: aws_sdk_dynamodb::types::error::InvalidEndpointException,
},

ProvisionedThroughputExceededException {
    error: aws_sdk_dynamodb::types::error::ProvisionedThroughputExceededException,
},

IdempotentParameterMismatchException {
    error: aws_sdk_dynamodb::types::error::IdempotentParameterMismatchException,
},

RequestLimitExceeded {
    error: aws_sdk_dynamodb::types::error::RequestLimitExceeded,
},

LimitExceededException {
    error: aws_sdk_dynamodb::types::error::LimitExceededException,
},

TransactionInProgressException {
    error: aws_sdk_dynamodb::types::error::TransactionInProgressException,
},
    Opaque {
        obj: ::dafny_runtime::Object<dyn ::std::any::Any>,
    },
}

impl ::std::cmp::Eq for Error {}

impl ::std::fmt::Display for Error {
    fn fmt(&self, f: &mut ::std::fmt::Formatter) -> ::std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

impl ::std::error::Error for Error {}
