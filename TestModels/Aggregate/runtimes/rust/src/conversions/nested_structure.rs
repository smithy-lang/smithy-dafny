// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::types::NestedStructure,
) -> ::std::rc::Rc<
    crate::r#simple::aggregate::internaldafny::types::NestedStructure,
> {
    ::std::rc::Rc::new(to_dafny_plain(value))
}

#[allow(dead_code)]
pub fn to_dafny_plain(
    value: crate::types::NestedStructure,
) -> crate::r#simple::aggregate::internaldafny::types::NestedStructure {
    crate::r#simple::aggregate::internaldafny::types::NestedStructure::NestedStructure {
        stringStructure: ::std::rc::Rc::new(match &value.string_structure {
    Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::conversions::string_structure::to_dafny(x.clone()) },
    None => crate::_Wrappers_Compile::Option::None { }
})
,
    }
}

#[allow(dead_code)]
pub fn option_to_dafny(
  value: ::std::option::Option<crate::types::NestedStructure>,
) -> ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
  crate::r#simple::aggregate::internaldafny::types::NestedStructure,
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
        crate::r#simple::aggregate::internaldafny::types::NestedStructure,
    >,
) -> crate::types::NestedStructure {
    plain_from_dafny(&*dafny_value)
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value: &crate::r#simple::aggregate::internaldafny::types::NestedStructure,
) -> crate::types::NestedStructure {
    match dafny_value {
        crate::r#simple::aggregate::internaldafny::types::NestedStructure::NestedStructure {..} =>
            crate::types::NestedStructure::builder()
                .set_string_structure(match (*dafny_value.stringStructure()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(crate::conversions::string_structure::from_dafny(value.clone())),
    _ => None,
}
)
                .build()
                .unwrap()
    }
}

#[allow(dead_code)]
pub fn option_from_dafny(
    dafny_value: ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
        crate::r#simple::aggregate::internaldafny::types::NestedStructure,
    >>>,
) -> ::std::option::Option<crate::types::NestedStructure> {
    match &*dafny_value {
        crate::_Wrappers_Compile::Option::Some { value } => {
            ::std::option::Option::Some(plain_from_dafny(value))
        }
        _ => ::std::option::Option::None,
    }
}
