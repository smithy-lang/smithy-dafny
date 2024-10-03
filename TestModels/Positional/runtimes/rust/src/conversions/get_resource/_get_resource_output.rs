// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_resource::GetResourceOutput,
) -> ::std::rc::Rc<
    crate::r#simple::positional::internaldafny::types::GetResourceOutput,
>{
    ::std::rc::Rc::new(crate::r#simple::positional::internaldafny::types::GetResourceOutput::GetResourceOutput {
        output: crate::conversions::simple_resource::to_dafny(value.output.clone().unwrap())
,
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::positional::internaldafny::types::GetResourceOutput,
    >,
) -> crate::operation::get_resource::GetResourceOutput {
    crate::operation::get_resource::GetResourceOutput::builder()
        .set_output(Some( crate::conversions::simple_resource::from_dafny(dafny_value.output().clone())
 ))
        .build()
        .unwrap()
}
