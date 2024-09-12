// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_resource::GetResourceInput,
) -> ::std::rc::Rc<
    crate::r#simple::positional::internaldafny::types::GetResourceInput,
>{
    ::std::rc::Rc::new(crate::r#simple::positional::internaldafny::types::GetResourceInput::GetResourceInput {
        name: crate::standard_library_conversions::ostring_to_dafny(&value.name) .Extract(),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::positional::internaldafny::types::GetResourceInput,
    >,
) -> crate::operation::get_resource::GetResourceInput {
    crate::operation::get_resource::GetResourceInput::builder()
        .set_name(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.name()) ))
        .build()
        .unwrap()
}
