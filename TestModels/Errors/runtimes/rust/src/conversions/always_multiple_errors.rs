// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.

use std::any::Any;

#[allow(dead_code)]
pub fn to_dafny_error(
    value: crate::operation::always_multiple_errors::AlwaysMultipleErrorsError,
) -> ::std::rc::Rc<::simple_errors_dafny::r#_simple_derrors_dinternaldafny_dtypes::Error> {
    match value {
        crate::operation::always_multiple_errors::AlwaysMultipleErrorsError::Unhandled(
            unhandled,
        ) => ::std::rc::Rc::new(
            ::simple_errors_dafny::r#_simple_derrors_dinternaldafny_dtypes::Error::Opaque {
                obj: ::dafny_runtime::UpcastTo::<::dafny_runtime::Object<dyn Any>>::upcast_to(
                    ::dafny_runtime::object::new(unhandled),
                ),
            },
        ),
    }
}

#[allow(dead_code)]
pub fn from_dafny_error(
    dafny_value: ::std::rc::Rc<
        ::simple_errors_dafny::r#_simple_derrors_dinternaldafny_dtypes::Error,
    >,
) -> crate::operation::always_multiple_errors::AlwaysMultipleErrorsError {
    // TODO: Losing information here, but we have to figure out how to wrap an arbitrary Dafny value as std::error::Error
    if matches!(
        &dafny_value.as_ref(),
        ::simple_errors_dafny::r#_simple_derrors_dinternaldafny_dtypes::Error::CollectionOfErrors { .. }
    ) {
        let error_message = "TODO: can't get message yet";
        crate::operation::always_multiple_errors::AlwaysMultipleErrorsError::generic(
            ::aws_smithy_types::error::metadata::ErrorMetadata::builder()
                .message(error_message)
                .build(),
        )
    } else {
        crate::operation::always_multiple_errors::AlwaysMultipleErrorsError::generic(
            ::aws_smithy_types::error::metadata::ErrorMetadata::builder()
                .message("Opaque error")
                .build(),
        )
    }
}

pub mod _always_multiple_errors_input;

pub mod _always_multiple_errors_output;
