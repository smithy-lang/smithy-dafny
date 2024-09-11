// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

pub fn to_dafny(
    value: crate::types::simple_constructor_config::SimpleConstructorConfig,
) -> ::std::rc::Rc<
    crate::r#simple::constructor::internaldafny::types::SimpleConstructorConfig,
> {
    ::std::rc::Rc::new(to_dafny_plain(value))
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::constructor::internaldafny::types::SimpleConstructorConfig,
    >,
) -> crate::types::simple_constructor_config::SimpleConstructorConfig {
    plain_from_dafny(&*dafny_value)
}


#[allow(dead_code)]
pub fn to_dafny_plain(
    value: crate::types::simple_constructor_config::SimpleConstructorConfig,
) -> crate::r#simple::constructor::internaldafny::types::SimpleConstructorConfig {
    crate::r#simple::constructor::internaldafny::types::SimpleConstructorConfig::SimpleConstructorConfig {
        blobValue: crate::standard_library_conversions::oblob_to_dafny(&value.blob_value),
 booleanValue: crate::standard_library_conversions::obool_to_dafny(&value.boolean_value),
 stringValue: crate::standard_library_conversions::ostring_to_dafny(&value.string_value),
 integerValue: crate::standard_library_conversions::oint_to_dafny(value.integer_value),
 longValue: crate::standard_library_conversions::olong_to_dafny(&value.long_value),
    }
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value: &crate::r#simple::constructor::internaldafny::types::SimpleConstructorConfig,
) -> crate::types::simple_constructor_config::SimpleConstructorConfig {
    match dafny_value {
        crate::r#simple::constructor::internaldafny::types::SimpleConstructorConfig::SimpleConstructorConfig {..} =>
            crate::types::simple_constructor_config::SimpleConstructorConfig::builder()
                .set_blob_value(crate::standard_library_conversions::oblob_from_dafny(dafny_value.blobValue().clone()))
 .set_boolean_value(crate::standard_library_conversions::obool_from_dafny(dafny_value.booleanValue().clone()))
 .set_string_value(crate::standard_library_conversions::ostring_from_dafny(dafny_value.stringValue().clone()))
 .set_integer_value(crate::standard_library_conversions::oint_from_dafny(dafny_value.integerValue().clone()))
 .set_long_value(crate::standard_library_conversions::olong_from_dafny(dafny_value.longValue().clone()))
                .build()
                .unwrap()
    }
}
