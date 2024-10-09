// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[derive(::std::clone::Clone, ::std::fmt::Debug, ::std::cmp::PartialEq)]
pub enum Error {
    CustomKeyStoreNotFoundException {
    error: aws_sdk_kms::types::error::CustomKeyStoreNotFoundException,
},

CloudHsmClusterInUseException {
    error: aws_sdk_kms::types::error::CloudHsmClusterInUseException,
},

LimitExceededException {
    error: aws_sdk_kms::types::error::LimitExceededException,
},

KmsInternalException {
    error: aws_sdk_kms::types::error::KmsInternalException,
},

DisabledException {
    error: aws_sdk_kms::types::error::DisabledException,
},

InvalidGrantTokenException {
    error: aws_sdk_kms::types::error::InvalidGrantTokenException,
},

IncorrectKeyMaterialException {
    error: aws_sdk_kms::types::error::IncorrectKeyMaterialException,
},

IncorrectTrustAnchorException {
    error: aws_sdk_kms::types::error::IncorrectTrustAnchorException,
},

CloudHsmClusterNotActiveException {
    error: aws_sdk_kms::types::error::CloudHsmClusterNotActiveException,
},

KeyUnavailableException {
    error: aws_sdk_kms::types::error::KeyUnavailableException,
},

NotFoundException {
    error: aws_sdk_kms::types::error::NotFoundException,
},

InvalidAliasNameException {
    error: aws_sdk_kms::types::error::InvalidAliasNameException,
},

InvalidMarkerException {
    error: aws_sdk_kms::types::error::InvalidMarkerException,
},

InvalidImportTokenException {
    error: aws_sdk_kms::types::error::InvalidImportTokenException,
},

UnsupportedOperationException {
    error: aws_sdk_kms::types::error::UnsupportedOperationException,
},

CloudHsmClusterNotRelatedException {
    error: aws_sdk_kms::types::error::CloudHsmClusterNotRelatedException,
},

IncorrectKeyException {
    error: aws_sdk_kms::types::error::IncorrectKeyException,
},

AlreadyExistsException {
    error: aws_sdk_kms::types::error::AlreadyExistsException,
},

CustomKeyStoreNameInUseException {
    error: aws_sdk_kms::types::error::CustomKeyStoreNameInUseException,
},

DependencyTimeoutException {
    error: aws_sdk_kms::types::error::DependencyTimeoutException,
},

InvalidArnException {
    error: aws_sdk_kms::types::error::InvalidArnException,
},

KmsInvalidStateException {
    error: aws_sdk_kms::types::error::KmsInvalidStateException,
},

ExpiredImportTokenException {
    error: aws_sdk_kms::types::error::ExpiredImportTokenException,
},

CloudHsmClusterInvalidConfigurationException {
    error: aws_sdk_kms::types::error::CloudHsmClusterInvalidConfigurationException,
},

CustomKeyStoreHasCmKsException {
    error: aws_sdk_kms::types::error::CustomKeyStoreHasCmKsException,
},

KmsInvalidSignatureException {
    error: aws_sdk_kms::types::error::KmsInvalidSignatureException,
},

InvalidKeyUsageException {
    error: aws_sdk_kms::types::error::InvalidKeyUsageException,
},

InvalidGrantIdException {
    error: aws_sdk_kms::types::error::InvalidGrantIdException,
},

TagException {
    error: aws_sdk_kms::types::error::TagException,
},

MalformedPolicyDocumentException {
    error: aws_sdk_kms::types::error::MalformedPolicyDocumentException,
},

CustomKeyStoreInvalidStateException {
    error: aws_sdk_kms::types::error::CustomKeyStoreInvalidStateException,
},

CloudHsmClusterNotFoundException {
    error: aws_sdk_kms::types::error::CloudHsmClusterNotFoundException,
},

InvalidCiphertextException {
    error: aws_sdk_kms::types::error::InvalidCiphertextException,
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
