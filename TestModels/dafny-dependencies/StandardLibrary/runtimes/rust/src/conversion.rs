use dafny_runtime::DafnyType;

use crate::implementation_from_dafny::*;

pub fn optional_to_dafny<R, D: DafnyType, F: FnOnce(&R) -> D>(f: F, input: &Option<R>) -> ::std::rc::Rc<_Wrappers_Compile::Option<D>>
{
    let dafny_value = match input {
        Some(r) => _Wrappers_Compile::Option::Some { value: f(r) },
        None => _Wrappers_Compile::Option::None {},
    };
    ::std::rc::Rc::new(dafny_value)
}

pub fn optional_from_dafny<R, D: DafnyType, F: FnOnce(&D) -> R>(f: F, input: &::std::rc::Rc<_Wrappers_Compile::Option<D>>) -> Option<R>
{
    if matches!(input.as_ref(), _Wrappers_Compile::Option::Some { .. }) {
        Some(f(&input.Extract()))
    } else {
        None
    }
}

pub fn ostring_to_dafny(
    input: &Option<String>,
) -> ::std::rc::Rc<
    _Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>,
> {
    let dafny_value = match input {
    Some(b) => _Wrappers_Compile::Option::Some { value:
        dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&b)
        },
    None => _Wrappers_Compile::Option::None {},
};
    ::std::rc::Rc::new(dafny_value)
}

pub fn ostring_from_dafny(
    input: ::std::rc::Rc<
        _Wrappers_Compile::Option<::dafny_runtime::Sequence<::dafny_runtime::DafnyCharUTF16>>,
    >,
) -> Option<String> {
    if matches!(input.as_ref(), _Wrappers_Compile::Option::Some { .. }) {
        Some(
            dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(
                &input.Extract(),
            ),
        )
    } else {
        None
    }
}

pub fn obool_to_dafny(input: Option<bool>) -> ::std::rc::Rc<_Wrappers_Compile::Option<bool>> {
    let dafny_value = match input {
        Some(b) => _Wrappers_Compile::Option::Some { value: b },
        None => _Wrappers_Compile::Option::None {},
    };
    ::std::rc::Rc::new(dafny_value)
}

pub fn obool_from_dafny(input: ::std::rc::Rc<_Wrappers_Compile::Option<bool>>) -> Option<bool> {
    if matches!(input.as_ref(), _Wrappers_Compile::Option::Some { .. }) {
        Some(input.Extract())
    } else {
        None
    }
}

pub fn oint_to_dafny(input: Option<i32>) -> ::std::rc::Rc<_Wrappers_Compile::Option<i32>> {
    let dafny_value = match input {
        Some(b) => _Wrappers_Compile::Option::Some { value: b },
        None => _Wrappers_Compile::Option::None {},
    };
    ::std::rc::Rc::new(dafny_value)
}

pub fn oint_from_dafny(input: ::std::rc::Rc<_Wrappers_Compile::Option<i32>>) -> Option<i32> {
    if matches!(input.as_ref(), _Wrappers_Compile::Option::Some { .. }) {
        Some(input.Extract())
    } else {
        None
    }
}

pub fn olong_to_dafny(input: Option<i64>) -> ::std::rc::Rc<_Wrappers_Compile::Option<i64>> {
    let dafny_value = match input {
        Some(b) => _Wrappers_Compile::Option::Some { value: b },
        None => _Wrappers_Compile::Option::None {},
    };
    ::std::rc::Rc::new(dafny_value)
}

pub fn olong_from_dafny(input: ::std::rc::Rc<_Wrappers_Compile::Option<i64>>) -> Option<i64> {
    if matches!(input.as_ref(), _Wrappers_Compile::Option::Some { .. }) {
        Some(input.Extract())
    } else {
        None
    }
}

pub fn oblob_to_dafny(
    input: &Option<::aws_smithy_types::Blob>,
) -> ::std::rc::Rc<_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>> {
    let dafny_value = match input {
        Some(b) => _Wrappers_Compile::Option::Some {
            value: ::dafny_runtime::Sequence::from_array(&b.clone().into_inner()),
        },
        None => _Wrappers_Compile::Option::None {},
    };
    ::std::rc::Rc::new(dafny_value)
}

pub fn oblob_from_dafny(
    input: ::std::rc::Rc<_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>>,
) -> Option<::aws_smithy_types::Blob> {
    if matches!(input.as_ref(), _Wrappers_Compile::Option::Some { .. }) {
        Some(
            ::aws_smithy_types::Blob::new(
                ::std::rc::Rc::try_unwrap(input.Extract().to_array())
                    .unwrap_or_else(|rc| (*rc).clone()),
            )
        )
    } else {
        None
    }
}
