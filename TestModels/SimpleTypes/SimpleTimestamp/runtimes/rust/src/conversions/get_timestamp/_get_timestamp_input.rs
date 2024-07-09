// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_timestamp::GetTimestampInput,
) -> ::std::rc::Rc<
    ::simple_timestamp_dafny::r#_simple_dtypes_dtimestamp_dinternaldafny_dtypes::GetTimestampInput,
> {
    let dafny_value = match value.value {
        Some(s) => ::simple_timestamp_dafny::_Wrappers_Compile::Option::Some { value: ::dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&s.to_string()) },
        None => ::simple_timestamp_dafny::_Wrappers_Compile::Option::None {},
    };
    ::std::rc::Rc::new(::simple_timestamp_dafny::r#_simple_dtypes_dtimestamp_dinternaldafny_dtypes::GetTimestampInput::GetTimestampInput {
    value: ::std::rc::Rc::new(dafny_value)
  })
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        ::simple_timestamp_dafny::r#_simple_dtypes_dtimestamp_dinternaldafny_dtypes::GetTimestampInput,
    >,
) -> Result<
    crate::operation::get_timestamp::GetTimestampInput,
    aws_smithy_types::date_time::DateTimeParseError,
> {
    let value = match dafny_value.value().as_ref() {
        simple_timestamp_dafny::_Wrappers_Compile::Option::None {} => None,
        simple_timestamp_dafny::_Wrappers_Compile::Option::Some { value } => {
            let value = dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(&value);
            let value = ::aws_smithy_types::DateTime::from_str(
                &value,
                aws_smithy_types::date_time::Format::DateTime,
            )?;
            Some(value)
        }
        simple_timestamp_dafny::_Wrappers_Compile::Option::_PhantomVariant(_) => unreachable!(),
    };

    Ok(crate::operation::get_timestamp::GetTimestampInput { value })
}
