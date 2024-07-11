// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(dead_code)]

pub fn to_dafny(
    value: aws_sdk_kms::types::KeyEncryptionMechanism,
) -> ::std::rc::Rc<::kms_lite_dafny::_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyEncryptionMechanism> {
    match value {
      aws_sdk_kms::types::KeyEncryptionMechanism::RsaesOaepSha256 => ::std::rc::Rc::new(::kms_lite_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyEncryptionMechanism::RSAES_OAEP_SHA_256 {}),
      _ => panic!()
    }
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: &::kms_lite_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyEncryptionMechanism,
) -> aws_sdk_kms::types::KeyEncryptionMechanism {
    match dafny_value {
      ::kms_lite_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::KeyEncryptionMechanism::RSAES_OAEP_SHA_256 {} => aws_sdk_kms::types::KeyEncryptionMechanism::RsaesOaepSha256,
    }
}
