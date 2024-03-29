pub fn to_dafny(value: crate::operation::get_string::GetStringInput) -> ::std::rc::Rc<crate::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringInput> {
  let dafny_value = 
    match value.value {
      Some(s) => crate::implementation_from_dafny::_Wrappers_Compile::Option::Some { 
        value: dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&s) 
      },
      None => crate::implementation_from_dafny::_Wrappers_Compile::Option::None {},
    };
  ::std::rc::Rc::new(crate::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringInput::GetStringInput {
    value: ::std::rc::Rc::new(dafny_value)
  })
}

pub fn from_dafny(dafny_value: ::std::rc::Rc<crate::implementation_from_dafny::r#_simple_dtypes_dsmithystring_dinternaldafny_dtypes::GetStringInput>) -> crate::operation::get_string::GetStringInput {
  let value = 
    match *dafny_value.value() {
      crate::implementation_from_dafny::_Wrappers_Compile::Option::Some { value } => Some(dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(&value)),
      crate::implementation_from_dafny::_Wrappers_Compile::Option::None {} => None,
      crate::implementation_from_dafny::_Wrappers_Compile::Option::_PhantomVariant(_) => panic!("Unreachable")
    };
    crate::operation::get_string::GetStringInput { value }
}