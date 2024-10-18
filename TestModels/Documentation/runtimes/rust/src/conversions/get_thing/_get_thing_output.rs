// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_thing::GetThingOutput,
) -> ::std::rc::Rc<
    crate::r#simple::documentation::internaldafny::types::GetThingOutput,
>{
    ::std::rc::Rc::new(crate::r#simple::documentation::internaldafny::types::GetThingOutput::GetThingOutput {
        thing: crate::conversions::thing::to_dafny(&value.thing.clone().unwrap())
,
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::documentation::internaldafny::types::GetThingOutput,
    >,
) -> crate::operation::get_thing::GetThingOutput {
    crate::operation::get_thing::GetThingOutput::builder()
        .set_thing(Some( crate::conversions::thing::from_dafny(dafny_value.thing().clone())
 ))
        .build()
        .unwrap()
}
