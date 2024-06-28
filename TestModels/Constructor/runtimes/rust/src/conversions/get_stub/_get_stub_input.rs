// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_stub::GetStubInput,
) -> ::std::rc::Rc<::stub_dafny::r#_stub_dinternaldafny_dtypes::GetStubInput> {
    let dafny_value = match value.value {
        Some(b) => ::stub_dafny::_Wrappers_Compile::Option::Some { value: b },
        None => ::stub_dafny::_Wrappers_Compile::Option::None {},
    };
    ::std::rc::Rc::new(
        ::stub_dafny::r#_stub_dinternaldafny_dtypes::GetStubInput::GetStubInput {
            value: ::std::rc::Rc::new(dafny_value),
        },
    )
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<::stub_dafny::r#_stub_dinternaldafny_dtypes::GetStubInput>,
) -> crate::operation::get_stub::GetStubInput {
    let value = if matches!(
        dafny_value.value().as_ref(),
        ::stub_dafny::_Wrappers_Compile::Option::Some { .. }
    ) {
        Some(dafny_value.value().Extract())
    } else if matches!(
        dafny_value.value().as_ref(),
        ::stub_dafny::_Wrappers_Compile::Option::None { .. }
    ) {
        None
    } else {
        panic!("Unreachable")
    };
    crate::operation::get_stub::GetStubInput { value }
}