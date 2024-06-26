use crate::implementation_from_dafny::*;

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
    input: &Option<Vec<u8>>,
) -> ::std::rc::Rc<_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>> {
    let dafny_value = match input {
        Some(b) => _Wrappers_Compile::Option::Some {
            value: ::dafny_runtime::Sequence::from_array(&b),
        },
        None => _Wrappers_Compile::Option::None {},
    };
    ::std::rc::Rc::new(dafny_value)
}

pub fn oblob_from_dafny(
    input: ::std::rc::Rc<_Wrappers_Compile::Option<::dafny_runtime::Sequence<u8>>>,
) -> Option<Vec<u8>> {
    if matches!(input.as_ref(), _Wrappers_Compile::Option::Some { .. }) {
        Some(
            ::std::rc::Rc::try_unwrap(input.Extract().to_array())
                .unwrap_or_else(|rc| (*rc).clone()),
        )
    } else {
        None
    }
}

// A wrapper for an arbitrary Dafny value to implement std::error::Error,
// since arbitrary Dafny values can be used as error values
// (usually as the "error" value in a Result.Failure)
pub struct DafnyError<T: ::dafny_runtime::DafnyType> {
    value: T,
}

pub fn error_from_dafny<T: ::dafny_runtime::DafnyType>(
    input: T
) -> DafnyError<T> {
    DafnyError { value: input }
}

impl<T: ::dafny_runtime::DafnyType> std::fmt::Display for DafnyError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value.fmt_print(f, false)
    }
}

impl<T: ::dafny_runtime::DafnyType> std::fmt::Debug for DafnyError<T> {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        self.value.fmt_print(f, false)
    }
}

impl<T: ::dafny_runtime::DafnyType> std::error::Error for DafnyError<T> {
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        None
    }

    fn cause(&self) -> Option<&dyn std::error::Error> {
        self.source()
    }
}