// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_blob::GetBlobOutput,
) -> ::std::rc::Rc<
    crate::r#simple::types::blob::internaldafny::types::GetBlobOutput,
>{
    ::std::rc::Rc::new(crate::r#simple::types::blob::internaldafny::types::GetBlobOutput::GetBlobOutput {
        value: crate::standard_library_conversions::oblob_to_dafny(&value.value),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::types::blob::internaldafny::types::GetBlobOutput,
    >,
) -> crate::operation::get_blob::GetBlobOutput {
    crate::operation::get_blob::GetBlobOutput::builder()
        .set_value(crate::standard_library_conversions::oblob_from_dafny(dafny_value.value().clone()))
        .build()
        .unwrap()
}
