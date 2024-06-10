// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_enum_third_known_value_test::GetEnumThirdKnownValueTestInput,
) -> ::std::rc::Rc<
    ::simple_enum_dafny::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumInput,
> {
    let dafny_value = match value.value {
        Some(v) => ::simple_enum_dafny::_Wrappers_Compile::Option::Some {
            value: ::std::rc::Rc::new(
                crate::conversions::simple_enum_shape::_simple_enum_shape::to_dafny(&v),
            ),
        },
        None => ::simple_enum_dafny::_Wrappers_Compile::Option::None {},
    };
    ::std::rc::Rc::new(::simple_enum_dafny::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumInput::GetEnumInput {
    value: ::std::rc::Rc::new(dafny_value)
  })
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        ::simple_enum_dafny::r#_simple_dtypes_dsmithyenum_dinternaldafny_dtypes::GetEnumInput,
    >,
) -> crate::operation::get_enum_third_known_value_test::GetEnumThirdKnownValueTestInput {
    let value = if matches!(
        dafny_value.value().as_ref(),
        ::simple_enum_dafny::_Wrappers_Compile::Option::Some { .. }
    ) {
        Some(
            crate::conversions::simple_enum_shape::_simple_enum_shape::from_dafny(
                &*dafny_value.value().Extract(),
            ),
        )
    } else if matches!(
        dafny_value.value().as_ref(),
        ::simple_enum_dafny::_Wrappers_Compile::Option::None { .. }
    ) {
        None
    } else {
        panic!("Unreachable")
    };
    crate::operation::get_enum_third_known_value_test::GetEnumThirdKnownValueTestInput { value }
}
