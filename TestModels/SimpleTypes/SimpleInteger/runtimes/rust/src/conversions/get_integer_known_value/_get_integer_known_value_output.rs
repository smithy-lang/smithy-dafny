// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_integer_known_value::GetIntegerKnownValueOutput,
) -> ::std::rc::Rc<
    ::simple_integer_dafny::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput,
> {
    let dafny_value = match value.value {
        Some(b) => ::simple_integer_dafny::_Wrappers_Compile::Option::Some { value: b },
        None => ::simple_integer_dafny::_Wrappers_Compile::Option::None {},
    };
    ::std::rc::Rc::new(::simple_integer_dafny::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput::GetIntegerOutput {
    value: ::std::rc::Rc::new(dafny_value)
  })
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        ::simple_integer_dafny::r#_simple_dtypes_dinteger_dinternaldafny_dtypes::GetIntegerOutput,
    >,
) -> crate::operation::get_integer_known_value::GetIntegerKnownValueOutput {
    let value = if matches!(
        dafny_value.value().as_ref(),
        ::simple_integer_dafny::_Wrappers_Compile::Option::Some { .. }
    ) {
        Some(dafny_value.value().Extract())
    } else if matches!(
        dafny_value.value().as_ref(),
        ::simple_integer_dafny::_Wrappers_Compile::Option::None { .. }
    ) {
        None
    } else {
        panic!("Unreachable")
    };
    crate::operation::get_integer_known_value::GetIntegerKnownValueOutput { value }
}