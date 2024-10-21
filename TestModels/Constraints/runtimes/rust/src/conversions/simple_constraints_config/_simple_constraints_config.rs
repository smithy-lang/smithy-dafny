// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

pub fn to_dafny(
    value: crate::types::simple_constraints_config::SimpleConstraintsConfig,
) -> ::std::rc::Rc<
    crate::r#simple::constraints::internaldafny::types::SimpleConstraintsConfig,
> {
    ::std::rc::Rc::new(to_dafny_plain(value))
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::constraints::internaldafny::types::SimpleConstraintsConfig,
    >,
) -> crate::types::simple_constraints_config::SimpleConstraintsConfig {
    plain_from_dafny(&*dafny_value)
}


#[allow(dead_code)]
pub fn to_dafny_plain(
    value: crate::types::simple_constraints_config::SimpleConstraintsConfig,
) -> crate::r#simple::constraints::internaldafny::types::SimpleConstraintsConfig {
    crate::r#simple::constraints::internaldafny::types::SimpleConstraintsConfig::SimpleConstraintsConfig {

    }
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value: &crate::r#simple::constraints::internaldafny::types::SimpleConstraintsConfig,
) -> crate::types::simple_constraints_config::SimpleConstraintsConfig {
    match dafny_value {
        crate::r#simple::constraints::internaldafny::types::SimpleConstraintsConfig::SimpleConstraintsConfig {..} =>
            crate::types::simple_constraints_config::SimpleConstraintsConfig::builder()

                .build()
                .unwrap()
    }
}
