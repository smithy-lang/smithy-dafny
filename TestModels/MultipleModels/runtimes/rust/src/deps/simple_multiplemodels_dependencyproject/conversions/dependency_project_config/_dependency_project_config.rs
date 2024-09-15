// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

pub fn to_dafny(
    value: crate::deps::simple_multiplemodels_dependencyproject::types::dependency_project_config::DependencyProjectConfig,
) -> ::std::rc::Rc<
    crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::DependencyProjectConfig,
> {
    ::std::rc::Rc::new(to_dafny_plain(value))
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::DependencyProjectConfig,
    >,
) -> crate::deps::simple_multiplemodels_dependencyproject::types::dependency_project_config::DependencyProjectConfig {
    plain_from_dafny(&*dafny_value)
}


#[allow(dead_code)]
pub fn to_dafny_plain(
    value: crate::deps::simple_multiplemodels_dependencyproject::types::dependency_project_config::DependencyProjectConfig,
) -> crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::DependencyProjectConfig {
    crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::DependencyProjectConfig::DependencyProjectConfig {

    }
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value: &crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::DependencyProjectConfig,
) -> crate::deps::simple_multiplemodels_dependencyproject::types::dependency_project_config::DependencyProjectConfig {
    match dafny_value {
        crate::r#simple::multiplemodels::dependencyproject::internaldafny::types::DependencyProjectConfig::DependencyProjectConfig {..} =>
            crate::deps::simple_multiplemodels_dependencyproject::types::dependency_project_config::DependencyProjectConfig::builder()

                .build()
                .unwrap()
    }
}
