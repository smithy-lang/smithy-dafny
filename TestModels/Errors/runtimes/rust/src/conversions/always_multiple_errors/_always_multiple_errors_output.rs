// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::always_multiple_errors::GetErrorsOutput,
) -> ::std::rc::Rc<
    crate::r#simple::errors::internaldafny::types::GetErrorsOutput,
>{
    ::std::rc::Rc::new(crate::r#simple::errors::internaldafny::types::GetErrorsOutput::GetErrorsOutput {
        value: crate::standard_library_conversions::ostring_to_dafny(&value.value),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::errors::internaldafny::types::GetErrorsOutput,
    >,
) -> crate::operation::always_multiple_errors::GetErrorsOutput {
    crate::operation::always_multiple_errors::GetErrorsOutput::builder()
        .set_value(crate::standard_library_conversions::ostring_from_dafny(dafny_value.value().clone()))
        .build()
        .unwrap()
}
