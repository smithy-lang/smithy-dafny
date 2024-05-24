// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_double::GetDoubleInput,
) -> ::std::rc::Rc<
    ::simple_double_dafny::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleInput,
> {
    let dafny_value = match value.value {
        Some(v) => ::simple_double_dafny::_Wrappers_Compile::Option::Some {
            value: v,
        },
        None => ::simple_double_dafny::_Wrappers_Compile::Option::None {},
    };
    ::std::rc::Rc::new(::simple_double_dafny::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleInput::GetDoubleInput {
    value: ::std::rc::Rc::new(dafny_value)
  })
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        ::simple_double_dafny::r#_simple_dtypes_dsmithydouble_dinternaldafny_dtypes::GetDoubleInput,
    >,
) -> crate::operation::get_double::GetDoubleInput {
    let value = if matches!(
        dafny_value.value().as_ref(),
        ::simple_double_dafny::_Wrappers_Compile::Option::Some { .. }
    ) {
        Some(dafny_value.value().Extract())
    } else if matches!(
        dafny_value.value().as_ref(),
        ::simple_double_dafny::_Wrappers_Compile::Option::None { .. }
    ) {
        None
    } else {
        panic!("Unreachable")
    };
    crate::operation::get_double::GetDoubleInput { value }
}
