// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: &crate::types::GetThingInput,
) -> ::std::rc::Rc<
    crate::r#simple::documentation::internaldafny::types::GetThingInput,
> {
    ::std::rc::Rc::new(to_dafny_plain(value.clone()))
}

#[allow(dead_code)]
pub fn to_dafny_plain(
    value: crate::types::GetThingInput,
) -> crate::r#simple::documentation::internaldafny::types::GetThingInput {
    crate::r#simple::documentation::internaldafny::types::GetThingInput::GetThingInput {
        name: crate::standard_library_conversions::ostring_to_dafny(&value.name) .Extract(),
    }
}

#[allow(dead_code)]
pub fn option_to_dafny(
  value: ::std::option::Option<crate::types::GetThingInput>,
) -> ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
  crate::r#simple::documentation::internaldafny::types::GetThingInput,
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
        crate::r#simple::documentation::internaldafny::types::GetThingInput,
    >,
) -> crate::types::GetThingInput {
    plain_from_dafny(&*dafny_value)
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value: &crate::r#simple::documentation::internaldafny::types::GetThingInput,
) -> crate::types::GetThingInput {
    match dafny_value {
        crate::r#simple::documentation::internaldafny::types::GetThingInput::GetThingInput {..} =>
            crate::types::GetThingInput::builder()
                .set_name(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.name()) ))
                .build()
                .unwrap()
    }
}

#[allow(dead_code)]
pub fn option_from_dafny(
    dafny_value: ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
        crate::r#simple::documentation::internaldafny::types::GetThingInput,
    >>>,
) -> ::std::option::Option<crate::types::GetThingInput> {
    match &*dafny_value {
        crate::_Wrappers_Compile::Option::Some { value } => {
            ::std::option::Option::Some(plain_from_dafny(value))
        }
        _ => ::std::option::Option::None,
    }
}
