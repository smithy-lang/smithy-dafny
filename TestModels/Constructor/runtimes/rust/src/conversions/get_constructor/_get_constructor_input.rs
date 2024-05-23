// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_constructor::GetConstructorInput,
) -> ::std::rc::Rc<
    ::constructor_dafny::_simple_dconstructor_dinternaldafny_dtypes::GetConstructorInput,
> {
    let dafny_value = match value.value {
            Some(s) => ::constructor_dafny::_Wrappers_Compile::Option::Some { value: dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&s) },
            None => ::constructor_dafny::_Wrappers_Compile::Option::None {},
        };
    ::std::rc::Rc::new(::constructor_dafny::_simple_dconstructor_dinternaldafny_dtypes::GetConstructorInput::GetConstructorInput {
            value: ::std::rc::Rc::new(dafny_value)
        })
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        ::constructor_dafny::_simple_dconstructor_dinternaldafny_dtypes::GetConstructorInput,
    >,
) -> crate::operation::get_constructor::GetConstructorInput {
    let value = if matches!(
        dafny_value.value().as_ref(),
        ::constructor_dafny::_Wrappers_Compile::Option::Some { .. }
    ) {
        Some(
            dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(
                &dafny_value.value().Extract(),
            ),
        )
    } else if matches!(
        dafny_value.value().as_ref(),
        ::constructor_dafny::_Wrappers_Compile::Option::None { .. }
    ) {
        None
    } else {
        panic!("Unreachable")
    };
    crate::operation::get_constructor::GetConstructorInput { value }
}
