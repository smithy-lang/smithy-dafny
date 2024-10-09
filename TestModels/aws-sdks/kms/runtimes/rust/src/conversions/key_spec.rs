// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

pub fn to_dafny(
    value: aws_sdk_kms::types::KeySpec,
) -> ::std::rc::Rc<crate::r#software::amazon::cryptography::services::kms::internaldafny::types::KeySpec>{
    ::std::rc::Rc::new(match value {
        aws_sdk_kms::types::KeySpec::Rsa2048 => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::KeySpec::RSA_2048 {},
aws_sdk_kms::types::KeySpec::Rsa3072 => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::KeySpec::RSA_3072 {},
aws_sdk_kms::types::KeySpec::Rsa4096 => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::KeySpec::RSA_4096 {},
aws_sdk_kms::types::KeySpec::EccNistP256 => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::KeySpec::ECC_NIST_P256 {},
aws_sdk_kms::types::KeySpec::EccNistP384 => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::KeySpec::ECC_NIST_P384 {},
aws_sdk_kms::types::KeySpec::EccNistP521 => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::KeySpec::ECC_NIST_P521 {},
aws_sdk_kms::types::KeySpec::EccSecgP256K1 => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::KeySpec::ECC_SECG_P256K1 {},
aws_sdk_kms::types::KeySpec::SymmetricDefault => crate::r#software::amazon::cryptography::services::kms::internaldafny::types::KeySpec::SYMMETRIC_DEFAULT {},
        _ => panic!("Unknown enum variant: {}", value),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: &crate::r#software::amazon::cryptography::services::kms::internaldafny::types::KeySpec,
) -> aws_sdk_kms::types::KeySpec {
    match dafny_value {
        crate::r#software::amazon::cryptography::services::kms::internaldafny::types::KeySpec::RSA_2048 {} => aws_sdk_kms::types::KeySpec::Rsa2048,
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::KeySpec::RSA_3072 {} => aws_sdk_kms::types::KeySpec::Rsa3072,
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::KeySpec::RSA_4096 {} => aws_sdk_kms::types::KeySpec::Rsa4096,
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::KeySpec::ECC_NIST_P256 {} => aws_sdk_kms::types::KeySpec::EccNistP256,
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::KeySpec::ECC_NIST_P384 {} => aws_sdk_kms::types::KeySpec::EccNistP384,
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::KeySpec::ECC_NIST_P521 {} => aws_sdk_kms::types::KeySpec::EccNistP521,
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::KeySpec::ECC_SECG_P256K1 {} => aws_sdk_kms::types::KeySpec::EccSecgP256K1,
crate::r#software::amazon::cryptography::services::kms::internaldafny::types::KeySpec::SYMMETRIC_DEFAULT {} => aws_sdk_kms::types::KeySpec::SymmetricDefault,
    }
}
