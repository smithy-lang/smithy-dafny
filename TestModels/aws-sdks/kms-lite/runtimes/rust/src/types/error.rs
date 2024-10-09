// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[derive(::std::clone::Clone, ::std::fmt::Debug, ::std::cmp::PartialEq)]
pub enum Error {
    KmsInvalidStateException {
    error: aws_sdk_kms::types::error::KmsInvalidStateException,
},

KmsInternalException {
    error: aws_sdk_kms::types::error::KmsInternalException,
},

InvalidArnException {
    error: aws_sdk_kms::types::error::InvalidArnException,
},

NotFoundException {
    error: aws_sdk_kms::types::error::NotFoundException,
},

DisabledException {
    error: aws_sdk_kms::types::error::DisabledException,
},

IncorrectKeyException {
    error: aws_sdk_kms::types::error::IncorrectKeyException,
},

DependencyTimeoutException {
    error: aws_sdk_kms::types::error::DependencyTimeoutException,
},

InvalidCiphertextException {
    error: aws_sdk_kms::types::error::InvalidCiphertextException,
},

UnsupportedOperationException {
    error: aws_sdk_kms::types::error::UnsupportedOperationException,
},

DryRunOperationException {
    error: aws_sdk_kms::types::error::DryRunOperationException,
},

KeyUnavailableException {
    error: aws_sdk_kms::types::error::KeyUnavailableException,
},

InvalidKeyUsageException {
    error: aws_sdk_kms::types::error::InvalidKeyUsageException,
},

InvalidGrantTokenException {
    error: aws_sdk_kms::types::error::InvalidGrantTokenException,
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
