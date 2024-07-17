// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

pub fn to_dafny(
    value: aws_sdk_kms::types::KeyUsageType,
) -> ::std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyUsageType>{
    ::std::rc::Rc::new(match value {
 aws_sdk_kms::types::KeyUsageType::SignVerify => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyUsageType::SIGN_VERIFY {},
 aws_sdk_kms::types::KeyUsageType::EncryptDecrypt => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyUsageType::ENCRYPT_DECRYPT {},
 aws_sdk_kms::types::KeyUsageType::GenerateVerifyMac => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyUsageType::GENERATE_VERIFY_MAC {},
 aws_sdk_kms::types::KeyUsageType::KeyAgreement => crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyUsageType::KEY_AGREEMENT {},
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
    dafny_value: &crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyUsageType,
) -> aws_sdk_kms::types::KeyUsageType {
    match dafny_value {
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyUsageType::SIGN_VERIFY {} => aws_sdk_kms::types::KeyUsageType::SignVerify,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyUsageType::ENCRYPT_DECRYPT {} => aws_sdk_kms::types::KeyUsageType::EncryptDecrypt,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyUsageType::GENERATE_VERIFY_MAC {} => aws_sdk_kms::types::KeyUsageType::GenerateVerifyMac,
 crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyUsageType::KEY_AGREEMENT {} => aws_sdk_kms::types::KeyUsageType::KeyAgreement,
    }
}
