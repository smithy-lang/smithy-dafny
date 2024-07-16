// Code generated by software.amazon.smithy.rust.codegen.smithy-rs. DO NOT EDIT.
#[allow(dead_code)]

pub fn to_dafny(
    config: crate::config::Config,
) -> ::std::rc::Rc<
    ::constructor_dafny::_simple_dconstructor_dinternaldafny_dtypes::SimpleConstructorConfig,
> {
    ::std::rc::Rc::new(
        ::constructor_dafny::_simple_dconstructor_dinternaldafny_dtypes::SimpleConstructorConfig::SimpleConstructorConfig { blobValue: blob_to_dafny(config.blob_value), booleanValue: boolean_to_dafny(config.boolean_value), stringValue: string_to_dafny(config.string_value), integerValue: integer_to_dafny(config.integer_value), longValue: long_to_dafny(config.long_value) })
}

fn blob_to_dafny(
    value: ::std::option::Option<::std::vec::Vec<u8>>,
) -> ::std::rc::Rc<::constructor_dafny::_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>> {
    let v = match value {
        Some(v) => ::constructor_dafny::_Wrappers_Compile::Option::Some {
            value: ::dafny_runtime::Sequence::from_array(&v),
        },
        None => ::constructor_dafny::_Wrappers_Compile::Option::None {},
    };

    ::std::rc::Rc::new(v)
}

fn boolean_to_dafny(
    value: ::std::option::Option<bool>,
) -> ::std::rc::Rc<::constructor_dafny::_Wrappers_Compile::Option<bool>> {
    let v = match value {
        Some(v) => ::constructor_dafny::_Wrappers_Compile::Option::Some { value: v },
        None => ::constructor_dafny::_Wrappers_Compile::Option::None {},
    };

    ::std::rc::Rc::new(v)
}

fn string_to_dafny(
    value: ::std::option::Option<::std::string::String>,
) -> ::std::rc::Rc<
    ::constructor_dafny::_Wrappers_Compile::Option<
        ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
    >,
> {
    let v = match value {
        Some(v) => ::constructor_dafny::_Wrappers_Compile::Option::Some { value: dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&v) },
        None => ::constructor_dafny::_Wrappers_Compile::Option::None {},
    };

    ::std::rc::Rc::new(v)
}

fn integer_to_dafny(
    value: ::std::option::Option<i32>,
) -> ::std::rc::Rc<::constructor_dafny::_Wrappers_Compile::Option<i32>> {
    let v = match value {
        Some(v) => ::constructor_dafny::_Wrappers_Compile::Option::Some { value: v },
        None => ::constructor_dafny::_Wrappers_Compile::Option::None {},
    };

    ::std::rc::Rc::new(v)
}

fn long_to_dafny(
    value: ::std::option::Option<i64>,
) -> ::std::rc::Rc<::constructor_dafny::_Wrappers_Compile::Option<i64>> {
    let v = match value {
        Some(v) => ::constructor_dafny::_Wrappers_Compile::Option::Some { value: v },
        None => ::constructor_dafny::_Wrappers_Compile::Option::None {},
    };

    ::std::rc::Rc::new(v)
}

#[allow(dead_code)]
pub fn from_dafny(
    config: ::std::rc::Rc<
        ::constructor_dafny::_simple_dconstructor_dinternaldafny_dtypes::SimpleConstructorConfig,
    >,
) -> crate::config::Config {
    crate::config::Config {
        blob_value: blob_from_dafny(config.blobValue().clone()),
        boolean_value: boolean_from_dafny(config.booleanValue().clone()),
        string_value: string_from_dafny(config.stringValue().clone()),
        integer_value: integer_from_dafny(config.integerValue().clone()),
        long_value: long_from_dafny(config.longValue().clone()),
    }
}

fn blob_from_dafny(
    value: ::std::rc::Rc<
        ::constructor_dafny::_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>,
    >,
) -> ::std::option::Option<::std::vec::Vec<u8>> {
    match value.as_ref() {
        ::constructor_dafny::_Wrappers_Compile::Option::Some { value } => {
            Some(::std::rc::Rc::try_unwrap(value.to_array()).unwrap_or_else(|rc| (*rc).clone()))
        }
        ::constructor_dafny::_Wrappers_Compile::Option::None {} => None,
        constructor_dafny::_Wrappers_Compile::Option::_PhantomVariant(_) => unreachable!(),
    }
}

fn boolean_from_dafny(
    value: ::std::rc::Rc<::constructor_dafny::_Wrappers_Compile::Option<bool>>,
) -> ::std::option::Option<bool> {
    match value.as_ref() {
        ::constructor_dafny::_Wrappers_Compile::Option::Some { value } => Some(*value),
        ::constructor_dafny::_Wrappers_Compile::Option::None {} => None,
        constructor_dafny::_Wrappers_Compile::Option::_PhantomVariant(_) => unreachable!(),
    }
}

fn string_from_dafny(
    value: ::std::rc::Rc<
        ::constructor_dafny::_Wrappers_Compile::Option<
            ::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>,
        >,
    >,
) -> ::std::option::Option<::std::string::String> {
    match value.as_ref() {
        ::constructor_dafny::_Wrappers_Compile::Option::Some { value } => Some(
            dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(
                value,
            ),
        ),
        ::constructor_dafny::_Wrappers_Compile::Option::None {} => None,
        constructor_dafny::_Wrappers_Compile::Option::_PhantomVariant(_) => unreachable!(),
    }
}

fn integer_from_dafny(
    value: ::std::rc::Rc<::constructor_dafny::_Wrappers_Compile::Option<i32>>,
) -> ::std::option::Option<i32> {
    match value.as_ref() {
        ::constructor_dafny::_Wrappers_Compile::Option::Some { value } => Some(*value),
        ::constructor_dafny::_Wrappers_Compile::Option::None {} => None,
        constructor_dafny::_Wrappers_Compile::Option::_PhantomVariant(_) => unreachable!(),
    }
}

fn long_from_dafny(
    value: ::std::rc::Rc<::constructor_dafny::_Wrappers_Compile::Option<i64>>,
) -> ::std::option::Option<i64> {
    match value.as_ref() {
        ::constructor_dafny::_Wrappers_Compile::Option::Some { value } => Some(*value),
        ::constructor_dafny::_Wrappers_Compile::Option::None {} => None,
        constructor_dafny::_Wrappers_Compile::Option::_PhantomVariant(_) => unreachable!(),
    }
}