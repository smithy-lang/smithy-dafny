// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_name::GetNameInput,
) -> ::std::rc::Rc<
    crate::r#simple::positional::internaldafny::types::GetNameInput,
>{
    ::std::rc::Rc::new(crate::r#simple::positional::internaldafny::types::GetNameInput::GetNameInput {

    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::positional::internaldafny::types::GetNameInput,
    >,
) -> crate::operation::get_name::GetNameInput {
    crate::operation::get_name::GetNameInput::builder()

        .build()
        .unwrap()
}
