// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(dead_code)]

pub fn to_dafny(
    value: crate::types::simple_documentation_config::SimpleDocumentationConfig,
) -> ::std::rc::Rc<
    crate::r#simple::documentation::internaldafny::types::SimpleDocumentationConfig,
> {
    ::std::rc::Rc::new(to_dafny_plain(value))
}

#[allow(dead_code)]
pub fn from_dafny(
    dafny_value: ::std::rc::Rc<
        crate::r#simple::documentation::internaldafny::types::SimpleDocumentationConfig,
    >,
) -> crate::types::simple_documentation_config::SimpleDocumentationConfig {
    plain_from_dafny(&*dafny_value)
}


#[allow(dead_code)]
pub fn to_dafny_plain(
    value: crate::types::simple_documentation_config::SimpleDocumentationConfig,
) -> crate::r#simple::documentation::internaldafny::types::SimpleDocumentationConfig {
    crate::r#simple::documentation::internaldafny::types::SimpleDocumentationConfig::SimpleDocumentationConfig {

    }
}

#[allow(dead_code)]
pub fn plain_from_dafny(
    dafny_value: &crate::r#simple::documentation::internaldafny::types::SimpleDocumentationConfig,
) -> crate::types::simple_documentation_config::SimpleDocumentationConfig {
    match dafny_value {
        crate::r#simple::documentation::internaldafny::types::SimpleDocumentationConfig::SimpleDocumentationConfig {..} =>
            crate::types::simple_documentation_config::SimpleDocumentationConfig::builder()

                .build()
                .unwrap()
    }
}
