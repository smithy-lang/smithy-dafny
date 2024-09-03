// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_string_known_value::GetStringInput,
) -> ::std::rc::Rc<
    crate::r#simple::types::smithystring::internaldafny::types::GetStringInput,
>{
    ::std::rc::Rc::new(crate::r#simple::types::smithystring::internaldafny::types::GetStringInput::GetStringInput {
        value: crate::standard_library_conversions::ostring_to_dafny(&value.value),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::types::smithystring::internaldafny::types::GetStringInput,
    >,
) -> crate::operation::get_string_known_value::GetStringInput {
    crate::operation::get_string_known_value::GetStringInput::builder()
        .set_value(crate::standard_library_conversions::ostring_from_dafny(dafny_value.value().clone()))
        .build()
        .unwrap()
}
