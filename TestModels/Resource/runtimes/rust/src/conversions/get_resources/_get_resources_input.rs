// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_resources::GetResourcesInput,
) -> ::std::rc::Rc<
    crate::r#simple::resources::internaldafny::types::GetResourcesInput,
>{
    ::std::rc::Rc::new(crate::r#simple::resources::internaldafny::types::GetResourcesInput::GetResourcesInput {
        value: crate::standard_library_conversions::ostring_to_dafny(&value.value),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::resources::internaldafny::types::GetResourcesInput,
    >,
) -> crate::operation::get_resources::GetResourcesInput {
    crate::operation::get_resources::GetResourcesInput::builder()
        .set_value(crate::standard_library_conversions::ostring_from_dafny(dafny_value.value().clone()))
        .build()
        .unwrap()
}
