// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetResourceInput {
    #[allow(missing_docs)] // documentation missing in model
pub name: ::std::option::Option<::std::string::String>,
}
impl GetResourceInput {
    #[allow(missing_docs)] // documentation missing in model
pub fn name(&self) -> &::std::option::Option<::std::string::String> {
    &self.name
}
}
impl GetResourceInput {
    /// Creates a new builder-style object to manufacture [`GetResourceInput`](crate::operation::get_resource::builders::GetResourceInput).
    pub fn builder() -> crate::operation::get_resource::builders::GetResourceInputBuilder {
        crate::operation::get_resource::builders::GetResourceInputBuilder::default()
    }
}

/// A builder for [`GetResourceInput`](crate::operation::operation::GetResourceInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetResourceInputBuilder {
    pub(crate) name: ::std::option::Option<::std::string::String>,
}
impl GetResourceInputBuilder {
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
    /// Consumes the builder and constructs a [`GetResourceInput`](crate::operation::operation::GetResourceInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_resource::GetResourceInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_resource::GetResourceInput {
            name: self.name,
        })
    }
}
