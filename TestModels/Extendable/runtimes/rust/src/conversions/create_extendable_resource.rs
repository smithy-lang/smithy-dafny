// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.

use std::any::Any;

#[allow(dead_code)]
pub fn to_dafny_error(
    value: crate::operation::create_extendable_resource::CreateExtendableResourceError,
) -> ::std::rc::Rc<
    ::simple_extendable_dafny::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error,
> {
    match value {
    crate::operation::create_extendable_resource::CreateExtendableResourceError::Unhandled(unhandled) =>
      ::std::rc::Rc::new(::simple_extendable_dafny::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error::Opaque { obj: ::dafny_runtime::upcast_object()(::dafny_runtime::object::new(unhandled)) })
  }
}

#[allow(dead_code)]
pub fn from_dafny_error(
    dafny_value: ::std::rc::Rc<
        ::simple_extendable_dafny::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error,
    >,
) -> crate::operation::create_extendable_resource::CreateExtendableResourceError {
    // TODO: Losing information here, but we have to figure out how to wrap an arbitrary Dafny value as std::error::Error
    if matches!(&dafny_value.as_ref(), ::simple_extendable_dafny::r#_simple_dextendable_dresources_dinternaldafny_dtypes::Error::CollectionOfErrors { .. }) {
    let error_message = "TODO: can't get message yet";
    crate::operation::create_extendable_resource::CreateExtendableResourceError::generic(::aws_smithy_types::error::metadata::ErrorMetadata::builder().message(error_message).build())
  } else {
    crate::operation::create_extendable_resource::CreateExtendableResourceError::generic(::aws_smithy_types::error::metadata::ErrorMetadata::builder().message("Opaque error").build())
  }
}

pub mod _create_extendable_resource_input;

pub mod _create_extendable_resource_output;
