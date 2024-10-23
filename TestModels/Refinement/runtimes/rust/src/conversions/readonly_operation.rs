// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.

use std::any::Any;

#[allow(dead_code)]
pub fn to_dafny_error(
    value: crate::operation::readonly_operation::ReadonlyOperationError,
) -> ::std::rc::Rc<crate::r#simple::refinement::internaldafny::types::Error> {
    match value {
    crate::operation::readonly_operation::ReadonlyOperationError::Unhandled(unhandled) =>
      ::std::rc::Rc::new(crate::r#simple::refinement::internaldafny::types::Error::Opaque { obj: ::dafny_runtime::upcast_object()(::dafny_runtime::object::new(unhandled)), alt_text : ::dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string("foo") })
  }
}

#[allow(dead_code)]
pub fn from_dafny_error(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::refinement::internaldafny::types::Error,
    >,
) -> crate::operation::readonly_operation::ReadonlyOperationError {
    // TODO: Losing information here, but we have to figure out how to wrap an arbitrary Dafny value as std::error::Error
    if matches!(&dafny_value.as_ref(), crate::r#simple::refinement::internaldafny::types::Error::CollectionOfErrors { .. }) {
    let error_message = "TODO: can't get message yet";
    crate::operation::readonly_operation::ReadonlyOperationError::generic(::aws_smithy_types::error::metadata::ErrorMetadata::builder().message(error_message).build())
  } else {
    crate::operation::readonly_operation::ReadonlyOperationError::generic(::aws_smithy_types::error::metadata::ErrorMetadata::builder().message("Opaque error").build())
  }
}

pub mod _readonly_operation_input;

pub mod _readonly_operation_output;
