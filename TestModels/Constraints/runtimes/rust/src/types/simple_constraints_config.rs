// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct SimpleConstraintsConfig {

}
impl SimpleConstraintsConfig {

}
impl SimpleConstraintsConfig {
    /// Creates a new builder-style object to manufacture [`SimpleConstraintsConfig`](crate::types::SimpleConstraintsConfig).
    pub fn builder() -> crate::types::simple_constraints_config::SimpleConstraintsConfigBuilder {
        crate::types::simple_constraints_config::SimpleConstraintsConfigBuilder::default()
    }
}

/// A builder for [`SimpleConstraintsConfig`](crate::types::SimpleConstraintsConfig).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct SimpleConstraintsConfigBuilder {

}
impl SimpleConstraintsConfigBuilder {

    /// Consumes the builder and constructs a [`SimpleConstraintsConfig`](crate::types::SimpleConstraintsConfig).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::types::simple_constraints_config::SimpleConstraintsConfig,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::types::simple_constraints_config::SimpleConstraintsConfig {

        })
    }
}
