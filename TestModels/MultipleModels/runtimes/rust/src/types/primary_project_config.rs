// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct PrimaryProjectConfig {

}
impl PrimaryProjectConfig {

}
impl PrimaryProjectConfig {
    /// Creates a new builder-style object to manufacture [`PrimaryProjectConfig`](crate::types::PrimaryProjectConfig).
    pub fn builder() -> crate::types::primary_project_config::PrimaryProjectConfigBuilder {
        crate::types::primary_project_config::PrimaryProjectConfigBuilder::default()
    }
}

/// A builder for [`PrimaryProjectConfig`](crate::types::PrimaryProjectConfig).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct PrimaryProjectConfigBuilder {

}
impl PrimaryProjectConfigBuilder {

    /// Consumes the builder and constructs a [`PrimaryProjectConfig`](crate::types::PrimaryProjectConfig).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::types::primary_project_config::PrimaryProjectConfig,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::types::primary_project_config::PrimaryProjectConfig {

        })
    }
}
