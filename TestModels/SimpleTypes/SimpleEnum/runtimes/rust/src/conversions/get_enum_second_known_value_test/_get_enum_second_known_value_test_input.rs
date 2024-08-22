// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_enum_second_known_value_test::GetEnumSecondKnownValueTestInput,
) -> ::std::rc::Rc<
    crate::r#simple::types::smithyenum::internaldafny::types::GetEnumInput,
> {
    let dafny_value = match value.value {
        Some(v) => crate::_Wrappers_Compile::Option::Some {
            value: ::std::rc::Rc::new(
                crate::conversions::simple_enum_shape::_simple_enum_shape::to_dafny(&v),
            ),
        },
        None => crate::_Wrappers_Compile::Option::None {},
    };
    ::std::rc::Rc::new(crate::r#simple::types::smithyenum::internaldafny::types::GetEnumInput::GetEnumInput {
    value: ::std::rc::Rc::new(dafny_value)
  })
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::types::smithyenum::internaldafny::types::GetEnumInput,
    >,
) -> crate::operation::get_enum_second_known_value_test::GetEnumSecondKnownValueTestInput {
    let value = if matches!(
        dafny_value.value().as_ref(),
        crate::_Wrappers_Compile::Option::Some { .. }
    ) {
        Some(
            crate::conversions::simple_enum_shape::_simple_enum_shape::from_dafny(
                &*dafny_value.value().Extract(),
            ),
        )
    } else if matches!(
        dafny_value.value().as_ref(),
        crate::_Wrappers_Compile::Option::None { .. }
    ) {
        None
    } else {
        panic!("Unreachable")
    };
    crate::operation::get_enum_second_known_value_test::GetEnumSecondKnownValueTestInput { value }
}
