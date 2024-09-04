// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_blob_known_value_test::GetBlobInput,
) -> ::std::rc::Rc<
    crate::r#simple::types::blob::internaldafny::types::GetBlobInput,
>{
    ::std::rc::Rc::new(crate::r#simple::types::blob::internaldafny::types::GetBlobInput::GetBlobInput {
        value: crate::standard_library_conversions::oblob_to_dafny(&value.value),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::types::blob::internaldafny::types::GetBlobInput,
    >,
) -> crate::operation::get_blob_known_value_test::GetBlobInput {
    crate::operation::get_blob_known_value_test::GetBlobInput::builder()
        .set_value(crate::standard_library_conversions::oblob_from_dafny(dafny_value.value().clone()))
        .build()
        .unwrap()
}
