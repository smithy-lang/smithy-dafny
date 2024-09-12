// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct SimpleResourcesConfig {
    #[allow(missing_docs)] // documentation missing in model
pub name: ::std::option::Option<::std::string::String>,
}
impl SimpleResourcesConfig {
    #[allow(missing_docs)] // documentation missing in model
pub fn name(&self) -> &::std::option::Option<::std::string::String> {
    &self.name
}
}
impl SimpleResourcesConfig {
    /// Creates a new builder-style object to manufacture [`SimpleResourcesConfig`](crate::types::SimpleResourcesConfig).
    pub fn builder() -> crate::types::simple_resources_config::SimpleResourcesConfigBuilder {
        crate::types::simple_resources_config::SimpleResourcesConfigBuilder::default()
    }
}

/// A builder for [`SimpleResourcesConfig`](crate::types::SimpleResourcesConfig).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct SimpleResourcesConfigBuilder {
    pub(crate) name: ::std::option::Option<::std::string::String>,
}
impl SimpleResourcesConfigBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn name(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.name = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_name(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.name = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_name(&self) -> &::std::option::Option<::std::string::String> {
    &self.name
}
    /// Consumes the builder and constructs a [`SimpleResourcesConfig`](crate::types::SimpleResourcesConfig).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::types::simple_resources_config::SimpleResourcesConfig,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::types::simple_resources_config::SimpleResourcesConfig {
            name: self.name,
        })
    }
}
