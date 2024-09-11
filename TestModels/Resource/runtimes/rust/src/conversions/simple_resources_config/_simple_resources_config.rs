// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

pub fn to_dafny(
    value: crate::types::simple_resources_config::SimpleResourcesConfig,
) -> ::std::rc::Rc<
    crate::r#simple::resources::internaldafny::types::SimpleResourcesConfig,
> {
    ::std::rc::Rc::new(to_dafny_plain(value))
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::resources::internaldafny::types::SimpleResourcesConfig,
    >,
) -> crate::types::simple_resources_config::SimpleResourcesConfig {
    plain_from_dafny(&*dafny_value)
}


#[allow(dead_code)]
pub fn to_dafny_plain(
    value: crate::types::simple_resources_config::SimpleResourcesConfig,
) -> crate::r#simple::resources::internaldafny::types::SimpleResourcesConfig {
    crate::r#simple::resources::internaldafny::types::SimpleResourcesConfig::SimpleResourcesConfig {
        name: crate::standard_library_conversions::ostring_to_dafny(&value.name) .Extract(),
    }
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value: &crate::r#simple::resources::internaldafny::types::SimpleResourcesConfig,
) -> crate::types::simple_resources_config::SimpleResourcesConfig {
    match dafny_value {
        crate::r#simple::resources::internaldafny::types::SimpleResourcesConfig::SimpleResourcesConfig {..} =>
            crate::types::simple_resources_config::SimpleResourcesConfig::builder()
                .set_name(Some( dafny_runtime::dafny_runtime_conversions::unicode_chars_false::dafny_string_to_string(dafny_value.name()) ))
                .build()
                .unwrap()
    }
}
