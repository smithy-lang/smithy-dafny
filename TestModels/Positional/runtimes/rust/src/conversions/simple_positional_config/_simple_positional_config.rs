// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

pub fn to_dafny(
    value: crate::types::simple_positional_config::SimplePositionalConfig,
) -> ::std::rc::Rc<
    crate::r#simple::positional::internaldafny::types::SimplePositionalConfig,
> {
    ::std::rc::Rc::new(to_dafny_plain(value))
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::positional::internaldafny::types::SimplePositionalConfig,
    >,
) -> crate::types::simple_positional_config::SimplePositionalConfig {
    plain_from_dafny(&*dafny_value)
}


#[allow(dead_code)]
pub fn to_dafny_plain(
    value: crate::types::simple_positional_config::SimplePositionalConfig,
) -> crate::r#simple::positional::internaldafny::types::SimplePositionalConfig {
    crate::r#simple::positional::internaldafny::types::SimplePositionalConfig::SimplePositionalConfig {

    }
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value: &crate::r#simple::positional::internaldafny::types::SimplePositionalConfig,
) -> crate::types::simple_positional_config::SimplePositionalConfig {
    match dafny_value {
        crate::r#simple::positional::internaldafny::types::SimplePositionalConfig::SimplePositionalConfig {..} =>
            crate::types::simple_positional_config::SimplePositionalConfig::builder()

                .build()
                .unwrap()
    }
}
