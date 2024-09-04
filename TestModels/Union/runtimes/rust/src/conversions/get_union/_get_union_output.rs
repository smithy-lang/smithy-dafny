// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_union::GetUnionOutput,
) -> ::std::rc::Rc<
    crate::r#simple::union::internaldafny::types::GetUnionOutput,
>{
    ::std::rc::Rc::new(crate::r#simple::union::internaldafny::types::GetUnionOutput::GetUnionOutput {
        union: ::std::rc::Rc::new(match &value.union {
    Some(x) => crate::_Wrappers_Compile::Option::Some { value: crate::conversions::my_union::to_dafny(x.clone()) },
    None => crate::_Wrappers_Compile::Option::None { }
})
,
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::union::internaldafny::types::GetUnionOutput,
    >,
) -> crate::operation::get_union::GetUnionOutput {
    crate::operation::get_union::GetUnionOutput::builder()
        .set_union(match (*dafny_value.union()).as_ref() {
    crate::r#_Wrappers_Compile::Option::Some { value } =>
        Some(crate::conversions::my_union::from_dafny(value.clone())),
    _ => None,
}
)
        .build()
        .unwrap()
}
