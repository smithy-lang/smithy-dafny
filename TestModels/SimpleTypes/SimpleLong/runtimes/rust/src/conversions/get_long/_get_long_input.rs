// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_long::GetLongInput,
) -> ::std::rc::Rc<
    crate::r#simple::types::smithylong::internaldafny::types::GetLongInput,
> {
    let dafny_value = match value.value {
        Some(v) => crate::_Wrappers_Compile::Option::Some { value: v },
        None => crate::_Wrappers_Compile::Option::None {},
    };
    ::std::rc::Rc::new(crate::r#simple::types::smithylong::internaldafny::types::GetLongInput::GetLongInput {
    value: ::std::rc::Rc::new(dafny_value)
  })
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::types::smithylong::internaldafny::types::GetLongInput,
    >,
) -> crate::operation::get_long::GetLongInput {
    let value = if matches!(
        dafny_value.value().as_ref(),
        crate::_Wrappers_Compile::Option::Some { .. }
    ) {
        Some(dafny_value.value().Extract())
    } else if matches!(
        dafny_value.value().as_ref(),
        crate::_Wrappers_Compile::Option::None { .. }
    ) {
        None
    } else {
        panic!("Unreachable")
    };
    crate::operation::get_long::GetLongInput { value }
}
