pub fn to_dafny(value: crate::operation::get_string::GetStringOutput) -> ::std::rc::Rc<crate::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput> {
  let dafny_value = 
    match value.value {
      Some(s) => crate::implementation_from_dafny::_Wrappers_Compile::Option::Some { 
        value: dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&s) 
      },
      None => crate::implementation_from_dafny::_Wrappers_Compile::Option::None {},
    };
  ::std::rc::Rc::new(crate::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput::GetStringOutput {
    value: ::std::rc::Rc::new(dafny_value)
  })
}

pub fn from_dafny(dafny_value: &::std::rc::Rc<crate::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput>) -> crate::operation::get_string::GetStringOutput {
  let value = 
    if matches!((&dafny_value.value()).as_ref(), crate::implementation_from_dafny::_Wrappers_Compile::Option::Some { .. }) {
      Some(dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(&dafny_value.value().Extract()))
    } else if matches!((&dafny_value.value()).as_ref(), crate::implementation_from_dafny::_Wrappers_Compile::Option::None { .. }) {
      None
    } else {
      panic!("Unreachable")
    };
  crate::operation::get_string::GetStringOutput { value }
}