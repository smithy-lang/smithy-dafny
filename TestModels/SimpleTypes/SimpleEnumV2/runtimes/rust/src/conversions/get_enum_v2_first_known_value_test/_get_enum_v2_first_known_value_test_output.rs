// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_enum_v2_first_known_value_test::GetEnumV2FirstKnownValueTestOutput,
) -> ::std::rc::Rc<
    ::simple_enum_v2_dafny::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
> {
    let dafny_value = match value.value {
        Some(b) => ::simple_enum_v2_dafny::_Wrappers_Compile::Option::Some {
            value: ::std::rc::Rc::new(
                crate::conversions::simple_enum_v2_shape::_simple_enum_v2_shape::to_dafny(&b),
            ),
        },
        None => ::simple_enum_v2_dafny::_Wrappers_Compile::Option::None {},
    };
    ::std::rc::Rc::new(::simple_enum_v2_dafny::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output::GetEnumV2Output {
    value: ::std::rc::Rc::new(dafny_value)
  })
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        ::simple_enum_v2_dafny::r#_simple_dtypes_denumv2_dinternaldafny_dtypes::GetEnumV2Output,
    >,
) -> crate::operation::get_enum_v2_first_known_value_test::GetEnumV2FirstKnownValueTestOutput {
    let value = if matches!(
        dafny_value.value().as_ref(),
        ::simple_enum_v2_dafny::_Wrappers_Compile::Option::Some { .. }
    ) {
        Some(
            crate::conversions::simple_enum_v2_shape::_simple_enum_v2_shape::from_dafny(
                &*dafny_value.value().Extract(),
            ),
        )
    } else if matches!(
        dafny_value.value().as_ref(),
        ::simple_enum_v2_dafny::_Wrappers_Compile::Option::None { .. }
    ) {
        None
    } else {
        panic!("Unreachable")
    };
    crate::operation::get_enum_v2_first_known_value_test::GetEnumV2FirstKnownValueTestOutput { value }
}
