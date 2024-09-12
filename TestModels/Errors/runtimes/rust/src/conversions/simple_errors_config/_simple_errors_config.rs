// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

pub fn to_dafny(
    value: crate::types::simple_errors_config::SimpleErrorsConfig,
) -> ::std::rc::Rc<
    crate::r#simple::errors::internaldafny::types::SimpleErrorsConfig,
> {
    ::std::rc::Rc::new(to_dafny_plain(value))
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::errors::internaldafny::types::SimpleErrorsConfig,
    >,
) -> crate::types::simple_errors_config::SimpleErrorsConfig {
    plain_from_dafny(&*dafny_value)
}


#[allow(dead_code)]
pub fn to_dafny_plain(
    value: crate::types::simple_errors_config::SimpleErrorsConfig,
) -> crate::r#simple::errors::internaldafny::types::SimpleErrorsConfig {
    crate::r#simple::errors::internaldafny::types::SimpleErrorsConfig::SimpleErrorsConfig {

    }
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value: &crate::r#simple::errors::internaldafny::types::SimpleErrorsConfig,
) -> crate::types::simple_errors_config::SimpleErrorsConfig {
    match dafny_value {
        crate::r#simple::errors::internaldafny::types::SimpleErrorsConfig::SimpleErrorsConfig {..} =>
            crate::types::simple_errors_config::SimpleErrorsConfig::builder()

                .build()
                .unwrap()
    }
}
