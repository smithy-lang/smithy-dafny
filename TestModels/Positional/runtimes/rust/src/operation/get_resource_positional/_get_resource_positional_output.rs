// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetResourcePositionalOutput {
    #[allow(missing_docs)] // documentation missing in model
pub output: ::std::option::Option<crate::types::simple_resource::SimpleResourceRef>,
}
impl GetResourcePositionalOutput {
    #[allow(missing_docs)] // documentation missing in model
pub fn output(&self) -> &::std::option::Option<crate::types::simple_resource::SimpleResourceRef> {
    &self.output
}
}
impl GetResourcePositionalOutput {
    /// Creates a new builder-style object to manufacture [`GetResourcePositionalOutput`](crate::operation::get_resource_positional::builders::GetResourcePositionalOutput).
    pub fn builder() -> crate::operation::get_resource_positional::builders::GetResourcePositionalOutputBuilder {
        crate::operation::get_resource_positional::builders::GetResourcePositionalOutputBuilder::default()
    }
}

/// A builder for [`GetResourcePositionalOutput`](crate::operation::operation::GetResourcePositionalOutput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetResourcePositionalOutputBuilder {
    pub(crate) output: ::std::option::Option<crate::types::simple_resource::SimpleResourceRef>,
}
impl GetResourcePositionalOutputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn output(mut self, input: impl ::std::convert::Into<crate::types::simple_resource::SimpleResourceRef>) -> Self {
    self.output = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_output(mut self, input: ::std::option::Option<crate::types::simple_resource::SimpleResourceRef>) -> Self {
    self.output = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_output(&self) -> &::std::option::Option<crate::types::simple_resource::SimpleResourceRef> {
    &self.output
}
    /// Consumes the builder and constructs a [`GetResourcePositionalOutput`](crate::operation::operation::GetResourcePositionalOutput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_resource_positional::GetResourcePositionalOutput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_resource_positional::GetResourcePositionalOutput {
            output: self.output,
        })
    }
}
