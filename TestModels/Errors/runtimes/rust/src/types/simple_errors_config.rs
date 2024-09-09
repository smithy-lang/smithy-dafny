// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct SimpleErrorsConfig {

}
impl SimpleErrorsConfig {

}
impl SimpleErrorsConfig {
    /// Creates a new builder-style object to manufacture [`SimpleErrorsConfig`](crate::types::SimpleErrorsConfig).
    pub fn builder() -> crate::types::simple_errors_config::SimpleErrorsConfigBuilder {
        crate::types::simple_errors_config::SimpleErrorsConfigBuilder::default()
    }
}

/// A builder for [`SimpleErrorsConfig`](crate::types::SimpleErrorsConfig).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct SimpleErrorsConfigBuilder {

}
impl SimpleErrorsConfigBuilder {

    /// Consumes the builder and constructs a [`SimpleErrorsConfig`](crate::types::SimpleErrorsConfig).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::types::simple_errors_config::SimpleErrorsConfig,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::types::simple_errors_config::SimpleErrorsConfig {

        })
    }
}
