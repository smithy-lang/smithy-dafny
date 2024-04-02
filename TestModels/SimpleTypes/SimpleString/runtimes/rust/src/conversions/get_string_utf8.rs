use std::any::Any;


pub fn to_dafny_error(value: crate::operation::get_string_utf8::GetStringUTF8Error) -> ::std::rc::Rc<crate::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::Error> {
  match value {
    crate::operation::get_string_utf8::GetStringUTF8Error::Unhandled(unhandled) => 
      ::std::rc::Rc::new(crate::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::Error::Opaque { obj: Box::into_raw(Box::new(unhandled) as Box<dyn Any>) })
  }
}

pub fn from_dafny_error(dafny_value: ::std::rc::Rc<crate::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::Error>) -> crate::operation::get_string_utf8::GetStringUTF8Error {
  // TODO: Losing information here, but we have to figure out how to wrap an arbitrary Dafny value as std::error::Error
  if matches!(&dafny_value.as_ref(), crate::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::Error::CollectionOfErrors { .. }) {
    let error_message = "TODO: can't get message yet";
    crate::operation::get_string_utf8::GetStringUTF8Error::generic(::aws_smithy_types::error::metadata::ErrorMetadata::builder().message(error_message).build())
  } else {
    crate::operation::get_string_utf8::GetStringUTF8Error::generic(::aws_smithy_types::error::metadata::ErrorMetadata::builder().message("Opaque error").build())
  }
}

pub mod _get_string_utf8_input;

pub mod _get_string_utf8_output;