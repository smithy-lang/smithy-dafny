// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]
pub fn to_dafny(
    value: crate::operation::get_constructor::GetConstructorOutput,
) -> ::std::rc::Rc<
    crate::r#simple::constructor::internaldafny::types::GetConstructorOutput,
>{
    ::std::rc::Rc::new(crate::r#simple::constructor::internaldafny::types::GetConstructorOutput::GetConstructorOutput {
        internalConfigString: crate::standard_library_conversions::ostring_to_dafny(&value.internal_config_string),
 blobValue: crate::standard_library_conversions::oblob_to_dafny(&value.blob_value),
 booleanValue: crate::standard_library_conversions::obool_to_dafny(&value.boolean_value),
 stringValue: crate::standard_library_conversions::ostring_to_dafny(&value.string_value),
 integerValue: crate::standard_library_conversions::oint_to_dafny(value.integer_value),
 longValue: crate::standard_library_conversions::olong_to_dafny(&value.long_value),
    })
}
 #[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::constructor::internaldafny::types::GetConstructorOutput,
    >,
) -> crate::operation::get_constructor::GetConstructorOutput {
    crate::operation::get_constructor::GetConstructorOutput::builder()
        .set_internal_config_string(crate::standard_library_conversions::ostring_from_dafny(dafny_value.internalConfigString().clone()))
 .set_blob_value(crate::standard_library_conversions::oblob_from_dafny(dafny_value.blobValue().clone()))
 .set_boolean_value(crate::standard_library_conversions::obool_from_dafny(dafny_value.booleanValue().clone()))
 .set_string_value(crate::standard_library_conversions::ostring_from_dafny(dafny_value.stringValue().clone()))
 .set_integer_value(crate::standard_library_conversions::oint_from_dafny(dafny_value.integerValue().clone()))
 .set_long_value(crate::standard_library_conversions::olong_from_dafny(dafny_value.longValue().clone()))
        .build()
        .unwrap()
}
