// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

pub fn to_dafny(
    value: aws_sdk_kms::types::SigningAlgorithmSpec,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec>{
    ::std::rc::Rc::new(match value {
 aws_sdk_kms::types::SigningAlgorithmSpec::RsassaPssSha256 => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec::RSASSA_PSS_SHA_256 {},
 aws_sdk_kms::types::SigningAlgorithmSpec::RsassaPssSha384 => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec::RSASSA_PSS_SHA_384 {},
 aws_sdk_kms::types::SigningAlgorithmSpec::RsassaPssSha512 => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec::RSASSA_PSS_SHA_512 {},
 aws_sdk_kms::types::SigningAlgorithmSpec::RsassaPkcs1V15Sha256 => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec::RSASSA_PKCS1_V1_5_SHA_256 {},
 aws_sdk_kms::types::SigningAlgorithmSpec::RsassaPkcs1V15Sha384 => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec::RSASSA_PKCS1_V1_5_SHA_384 {},
 aws_sdk_kms::types::SigningAlgorithmSpec::RsassaPkcs1V15Sha512 => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec::RSASSA_PKCS1_V1_5_SHA_512 {},
 aws_sdk_kms::types::SigningAlgorithmSpec::EcdsaSha256 => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec::ECDSA_SHA_256 {},
 aws_sdk_kms::types::SigningAlgorithmSpec::EcdsaSha384 => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec::ECDSA_SHA_384 {},
 aws_sdk_kms::types::SigningAlgorithmSpec::EcdsaSha512 => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec::ECDSA_SHA_512 {},
 aws_sdk_kms::types::SigningAlgorithmSpec::Sm2Dsa => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec::SM2DSA {},
        // TODO: This should not be a panic, but the Dafny image of the enum shape doesn't have an Unknown variant of any kind,
        // so there's no way to succeed.
        // See https://github.com/smithy-lang/smithy-dafny/issues/476.
        // This could be handled more cleanly if conversion functions returned Results,
        // but that would be a large and disruptive change to the overall code flow.
        _ => panic!("Unknown enum variant: {}", value),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: &crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec,
) -> aws_sdk_kms::types::SigningAlgorithmSpec {
    match dafny_value {
 crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec::RSASSA_PSS_SHA_256 {} => aws_sdk_kms::types::SigningAlgorithmSpec::RsassaPssSha256,
 crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec::RSASSA_PSS_SHA_384 {} => aws_sdk_kms::types::SigningAlgorithmSpec::RsassaPssSha384,
 crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec::RSASSA_PSS_SHA_512 {} => aws_sdk_kms::types::SigningAlgorithmSpec::RsassaPssSha512,
 crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec::RSASSA_PKCS1_V1_5_SHA_256 {} => aws_sdk_kms::types::SigningAlgorithmSpec::RsassaPkcs1V15Sha256,
 crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec::RSASSA_PKCS1_V1_5_SHA_384 {} => aws_sdk_kms::types::SigningAlgorithmSpec::RsassaPkcs1V15Sha384,
 crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec::RSASSA_PKCS1_V1_5_SHA_512 {} => aws_sdk_kms::types::SigningAlgorithmSpec::RsassaPkcs1V15Sha512,
 crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec::ECDSA_SHA_256 {} => aws_sdk_kms::types::SigningAlgorithmSpec::EcdsaSha256,
 crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec::ECDSA_SHA_384 {} => aws_sdk_kms::types::SigningAlgorithmSpec::EcdsaSha384,
 crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec::ECDSA_SHA_512 {} => aws_sdk_kms::types::SigningAlgorithmSpec::EcdsaSha512,
 crate::r#software::amazon::cryptography::services::kms::internaldafny::types::SigningAlgorithmSpec::SM2DSA {} => aws_sdk_kms::types::SigningAlgorithmSpec::Sm2Dsa,
    }
}
