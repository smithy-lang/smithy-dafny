// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_timestamp::GetTimestampOutput,
) -> ::std::rc::Rc<
    crate::r#simple::types::timestamp::internaldafny::types::GetTimestampOutput,
>{
    ::std::rc::Rc::new(crate::r#simple::types::timestamp::internaldafny::types::GetTimestampOutput::GetTimestampOutput {
        value: crate::standard_library_conversions::otimestamp_to_dafny(&value.value),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::types::timestamp::internaldafny::types::GetTimestampOutput,
    >,
) -> crate::operation::get_timestamp::GetTimestampOutput {
    crate::operation::get_timestamp::GetTimestampOutput::builder()
        .set_value(crate::standard_library_conversions::otimestamp_from_dafny(dafny_value.value().clone()))
        .build()
        .unwrap()
}
