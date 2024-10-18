// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
/// Fancy configuration things to make getting things even thingier.
pub struct SimpleDocumentationConfig {

}
impl SimpleDocumentationConfig {

}
impl SimpleDocumentationConfig {
    /// Creates a new builder-style object to manufacture [`SimpleDocumentationConfig`](crate::types::SimpleDocumentationConfig).
    pub fn builder() -> crate::types::simple_documentation_config::SimpleDocumentationConfigBuilder {
        crate::types::simple_documentation_config::SimpleDocumentationConfigBuilder::default()
    }
}

/// A builder for [`SimpleDocumentationConfig`](crate::types::SimpleDocumentationConfig).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct SimpleDocumentationConfigBuilder {

}
impl SimpleDocumentationConfigBuilder {

    /// Consumes the builder and constructs a [`SimpleDocumentationConfig`](crate::types::SimpleDocumentationConfig).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::types::simple_documentation_config::SimpleDocumentationConfig,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::types::simple_documentation_config::SimpleDocumentationConfig {

        })
    }
}
