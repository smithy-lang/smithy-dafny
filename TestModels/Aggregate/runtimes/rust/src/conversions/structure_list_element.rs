// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::types::StructureListElement,
) -> ::std::rc::Rc<
    crate::r#simple::aggregate::internaldafny::types::StructureListElement,
> {
    ::std::rc::Rc::new(to_dafny_plain(value))
}

#[allow(dead_code)]
pub fn to_dafny_plain(
    value: crate::types::StructureListElement,
) -> crate::r#simple::aggregate::internaldafny::types::StructureListElement {
    crate::r#simple::aggregate::internaldafny::types::StructureListElement::StructureListElement {
        stringValue: crate::standard_library_conversions::ostring_to_dafny(&value.string_value),
 integerValue: crate::standard_library_conversions::oint_to_dafny(value.integer_value),
    }
}

#[allow(dead_code)]
pub fn option_to_dafny(
  value: ::std::option::Option<crate::types::StructureListElement>,
) -> ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
  crate::r#simple::aggregate::internaldafny::types::StructureListElement,
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
        crate::r#simple::aggregate::internaldafny::types::StructureListElement,
    >,
) -> crate::types::StructureListElement {
    plain_from_dafny(&*dafny_value)
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value: &crate::r#simple::aggregate::internaldafny::types::StructureListElement,
) -> crate::types::StructureListElement {
    match dafny_value {
        crate::r#simple::aggregate::internaldafny::types::StructureListElement::StructureListElement {..} =>
            crate::types::StructureListElement::builder()
                .set_string_value(crate::standard_library_conversions::ostring_from_dafny(dafny_value.stringValue().clone()))
 .set_integer_value(crate::standard_library_conversions::oint_from_dafny(dafny_value.integerValue().clone()))
                .build()
                .unwrap()
    }
}

#[allow(dead_code)]
pub fn option_from_dafny(
    dafny_value: ::std::rc::Rc<crate::_Wrappers_Compile::Option<::std::rc::Rc<
        crate::r#simple::aggregate::internaldafny::types::StructureListElement,
    >>>,
) -> ::std::option::Option<crate::types::StructureListElement> {
    match &*dafny_value {
        crate::_Wrappers_Compile::Option::Some { value } => {
            ::std::option::Option::Some(plain_from_dafny(value))
        }
        _ => ::std::option::Option::None,
    }
}
