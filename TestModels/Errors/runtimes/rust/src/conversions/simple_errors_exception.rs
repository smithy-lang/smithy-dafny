// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::types::SimpleErrorsException,
) -> ::std::rc::Rc<
    crate::r#simple::errors::internaldafny::types::SimpleErrorsException,
> {
    ::std::rc::Rc::new(to_dafny_plain(value))
}

#[allow(dead_code)]
pub fn to_dafny_plain(
    value: crate::types::SimpleErrorsException,
) -> crate::r#simple::errors::internaldafny::types::SimpleErrorsException {
    crate::r#simple::errors::internaldafny::types::SimpleErrorsException::SimpleErrorsException {
        message: dafny_runtime::dafny_runtime_conversions::unicode_chars_false::string_to_dafny_string(&value.message),
    }
}

#[allow(dead_code)]
pub fn option_to_dafny(
  value: ::std::option::Option<crate::types::SimpleErrorsException>,
) -> ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
  crate::r#simple::errors::internaldafny::types::SimpleErrorsException,
>>>{
    ::std::rc::Rc::new(match value {
        ::std::option::Option::None => crate::_Wrappers_Compile::Option::None {},
        ::std::option::Option::Some(x) => crate::_Wrappers_Compile::Option::Some {
            value: ::std::rc::Rc::new(to_dafny_plain(x)),
        },
    })
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::errors::internaldafny::types::SimpleErrorsException,
    >,
) -> crate::types::SimpleErrorsException {
    plain_from_dafny(&*dafny_value)
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value: &crate::r#simple::errors::internaldafny::types::SimpleErrorsException,
) -> crate::types::SimpleErrorsException {
    match dafny_value {
        crate::r#simple::errors::internaldafny::types::SimpleErrorsException::SimpleErrorsException {..} =>
            crate::types::SimpleErrorsException::builder()
                .set_message(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.message()) ))
                .build()
                .unwrap()
    }
}

#[allow(dead_code)]
pub fn option_from_dafny(
    dafny_value: ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
        crate::r#simple::errors::internaldafny::types::SimpleErrorsException,
    >>>,
) -> ::std::option::Option<crate::types::SimpleErrorsException> {
    match &*dafny_value {
        crate::_Wrappers_Compile::Option::Some { value } => {
            ::std::option::Option::Some(plain_from_dafny(value))
        }
        _ => ::std::option::Option::None,
    }
}
