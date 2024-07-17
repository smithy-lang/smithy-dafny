// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

pub fn to_dafny(
    value: aws_sdk_kms::types::KeySpec,
) -> ::std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec>{
    ::std::rc::Rc::new(match value {
 aws_sdk_kms::types::KeySpec::Rsa2048 => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::RSA_2048 {},
 aws_sdk_kms::types::KeySpec::Rsa3072 => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::RSA_3072 {},
 aws_sdk_kms::types::KeySpec::Rsa4096 => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::RSA_4096 {},
 aws_sdk_kms::types::KeySpec::EccNistP256 => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::ECC_NIST_P256 {},
 aws_sdk_kms::types::KeySpec::EccNistP384 => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::ECC_NIST_P384 {},
 aws_sdk_kms::types::KeySpec::EccNistP521 => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::ECC_NIST_P521 {},
 aws_sdk_kms::types::KeySpec::EccSecgP256K1 => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::ECC_SECG_P256K1 {},
 aws_sdk_kms::types::KeySpec::SymmetricDefault => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::SYMMETRIC_DEFAULT {},
 aws_sdk_kms::types::KeySpec::Hmac224 => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::HMAC_224 {},
 aws_sdk_kms::types::KeySpec::Hmac256 => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::HMAC_256 {},
 aws_sdk_kms::types::KeySpec::Hmac384 => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::HMAC_384 {},
 aws_sdk_kms::types::KeySpec::Hmac512 => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::HMAC_512 {},
 aws_sdk_kms::types::KeySpec::Sm2 => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::SM2 {},
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
    dafny_value: &crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec,
) -> aws_sdk_kms::types::KeySpec {
    match dafny_value {
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::RSA_2048 {} => aws_sdk_kms::types::KeySpec::Rsa2048,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::RSA_3072 {} => aws_sdk_kms::types::KeySpec::Rsa3072,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::RSA_4096 {} => aws_sdk_kms::types::KeySpec::Rsa4096,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::ECC_NIST_P256 {} => aws_sdk_kms::types::KeySpec::EccNistP256,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::ECC_NIST_P384 {} => aws_sdk_kms::types::KeySpec::EccNistP384,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::ECC_NIST_P521 {} => aws_sdk_kms::types::KeySpec::EccNistP521,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::ECC_SECG_P256K1 {} => aws_sdk_kms::types::KeySpec::EccSecgP256K1,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::SYMMETRIC_DEFAULT {} => aws_sdk_kms::types::KeySpec::SymmetricDefault,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::HMAC_224 {} => aws_sdk_kms::types::KeySpec::Hmac224,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::HMAC_256 {} => aws_sdk_kms::types::KeySpec::Hmac256,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::HMAC_384 {} => aws_sdk_kms::types::KeySpec::Hmac384,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::HMAC_512 {} => aws_sdk_kms::types::KeySpec::Hmac512,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeySpec::SM2 {} => aws_sdk_kms::types::KeySpec::Sm2,
    }
}
