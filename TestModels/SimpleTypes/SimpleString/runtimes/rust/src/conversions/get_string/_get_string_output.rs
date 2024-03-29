
pub fn to_dafny(value: crate::operation::get_string::GetStringOutput) -> crate::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput {
  let dafny_value = 
    match value.value {
      Some(s) => crate::implementation_from_dafny::_Wrappers_Compile::Option::Some { value: dafny_runtime::string_utf16_of(&s) },
      None => crate::implementation_from_dafny::_Wrappers_Compile::Option::None {},
    };
  &::std::rc::Rc::new(crate::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput::GetStringOutput {
    value: ::std::rc::Rc::new(dafny_value)
  })
}

pub fn from_dafny(value: crate::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput) -> crate::operation::get_string::GetStringOutput {
  let dafny_value = 
    match value.value {
      crate::implementation_from_dafny::_Wrappers_Compile::Option::Some(s) => Some(dafny_runtime::string_utf16_of(&s)),
      crate::implementation_from_dafny::_Wrappers_Compile::Option::None => None,
    };
  &::std::rc::Rc::new(crate::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringOutput::GetStringOutput {
    value: ::std::rc::Rc::new(dafny_value)
  })
}