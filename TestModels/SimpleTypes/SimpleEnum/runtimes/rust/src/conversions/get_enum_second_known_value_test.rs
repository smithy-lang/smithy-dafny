// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.

use std::any::Any;

#[allow(dead_code)]
pub fn to_dafny_error(
    value: crate::operation::get_enum_second_known_value_test::GetEnumSecondKnownValueTestError,
) -> ::std::rc::Rc<::simple_enum_dafny::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error> {
    match value {
    crate::operation::get_enum_second_known_value_test::GetEnumSecondKnownValueTestError::Unhandled(unhandled) =>
      ::std::rc::Rc::new(::simple_enum_dafny::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error::Opaque { obj: ::dafny_runtime::UpcastTo::<::dafny_runtime::Object<dyn Any>>::upcast_to(::dafny_runtime::object::new(unhandled)) })
  }
}

#[allow(dead_code)]
pub fn from_dafny_error(
    dafny_value: ::std::rc::Rc<
        ::simple_enum_dafny::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error,
    >,
) -> crate::operation::get_enum_second_known_value_test::GetEnumSecondKnownValueTestError {
    // TODO: Losing information here, but we have to figure out how to wrap an arbitrary Dafny value as std::error::Error
    if matches!(&dafny_value.as_ref(), ::simple_enum_dafny::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::Error::CollectionOfErrors { .. }) {
    let error_message = "TODO: can't get message yet";
    crate::operation::get_enum_second_known_value_test::GetEnumSecondKnownValueTestError::generic(::aws_smithy_types::error::metadata::ErrorMetadata::builder().message(error_message).build())
  } else {
    crate::operation::get_enum_second_known_value_test::GetEnumSecondKnownValueTestError::generic(::aws_smithy_types::error::metadata::ErrorMetadata::builder().message("Opaque error").build())
  }
}

pub mod _get_enum_second_known_value_test_input;

pub mod _get_enum_second_known_value_test_output;
