pub mod _generate_data_key_request;

pub mod _generate_data_key_response;


use std::any::Any;

#[allow(dead_code)]
pub fn to_dafny_error(
    value: aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError,
) -> ::std::rc::Rc<crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error> {
  ::std::rc::Rc::new(crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error::Opaque { obj: ::dafny_runtime::upcast_object()(::dafny_runtime::object::new(value)) })
}

#[allow(dead_code)]
pub fn from_dafny_error(
    dafny_value: ::std::rc::Rc<
    crate::implementation_from_dafny::r#_software_damazon_dcryptography_dservices_dkms_dinternaldafny_dtypes::Error,
    >,
) -> aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError {
  // TODO: Losing information here, but we have to figure out how to wrap an arbitrary Dafny value as std::error::Error
  aws_sdk_kms::operation::generate_data_key::GenerateDataKeyError::generic(::aws_smithy_types::error::metadata::ErrorMetadata::builder().message("Opaque error").build())
}