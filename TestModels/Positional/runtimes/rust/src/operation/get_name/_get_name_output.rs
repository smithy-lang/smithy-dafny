// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetNameOutput {
    #[allow(missing_docs)] // documentation missing in model
pub name: ::std::option::Option<::std::string::String>,
}
impl GetNameOutput {
    #[allow(missing_docs)] // documentation missing in model
pub fn name(&self) -> &::std::option::Option<::std::string::String> {
    &self.name
}
}
impl GetNameOutput {
    /// Creates a new builder-style object to manufacture [`GetNameOutput`](crate::operation::get_name::builders::GetNameOutput).
    pub fn builder() -> crate::operation::get_name::builders::GetNameOutputBuilder {
        crate::operation::get_name::builders::GetNameOutputBuilder::default()
    }
}

/// A builder for [`GetNameOutput`](crate::operation::operation::GetNameOutput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetNameOutputBuilder {
    pub(crate) name: ::std::option::Option<::std::string::String>,
}
impl GetNameOutputBuilder {
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
    /// Consumes the builder and constructs a [`GetNameOutput`](crate::operation::operation::GetNameOutput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_name::GetNameOutput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_name::GetNameOutput {
            name: self.name,
        })
    }
}
