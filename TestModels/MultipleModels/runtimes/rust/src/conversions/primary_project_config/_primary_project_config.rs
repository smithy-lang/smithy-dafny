// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

pub fn to_dafny(
    value: crate::types::primary_project_config::PrimaryProjectConfig,
) -> ::std::rc::Rc<
    crate::r#simple::multiplemodels::primaryproject::internaldafny::types::PrimaryProjectConfig,
> {
    ::std::rc::Rc::new(to_dafny_plain(value))
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::multiplemodels::primaryproject::internaldafny::types::PrimaryProjectConfig,
    >,
) -> crate::types::primary_project_config::PrimaryProjectConfig {
    plain_from_dafny(&*dafny_value)
}


#[allow(dead_code)]
pub fn to_dafny_plain(
    value: crate::types::primary_project_config::PrimaryProjectConfig,
) -> crate::r#simple::multiplemodels::primaryproject::internaldafny::types::PrimaryProjectConfig {
    crate::r#simple::multiplemodels::primaryproject::internaldafny::types::PrimaryProjectConfig::PrimaryProjectConfig {

    }
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value: &crate::r#simple::multiplemodels::primaryproject::internaldafny::types::PrimaryProjectConfig,
) -> crate::types::primary_project_config::PrimaryProjectConfig {
    match dafny_value {
        crate::r#simple::multiplemodels::primaryproject::internaldafny::types::PrimaryProjectConfig::PrimaryProjectConfig {..} =>
            crate::types::primary_project_config::PrimaryProjectConfig::builder()

                .build()
                .unwrap()
    }
}
