// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetResourcesOutput {
    #[allow(missing_docs)] // documentation missing in model
pub output: ::std::option::Option<crate::types::simple_resource::SimpleResourceRef>,
}
impl GetResourcesOutput {
    #[allow(missing_docs)] // documentation missing in model
pub fn output(&self) -> &::std::option::Option<crate::types::simple_resource::SimpleResourceRef> {
    &self.output
}
}
impl GetResourcesOutput {
    /// Creates a new builder-style object to manufacture [`GetResourcesOutput`](crate::operation::get_resources::builders::GetResourcesOutput).
    pub fn builder() -> crate::operation::get_resources::builders::GetResourcesOutputBuilder {
        crate::operation::get_resources::builders::GetResourcesOutputBuilder::default()
    }
}

/// A builder for [`GetResourcesOutput`](crate::operation::operation::GetResourcesOutput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetResourcesOutputBuilder {
    pub(crate) output: ::std::option::Option<crate::types::simple_resource::SimpleResourceRef>,
}
impl GetResourcesOutputBuilder {
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
    /// Consumes the builder and constructs a [`GetResourcesOutput`](crate::operation::operation::GetResourcesOutput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_resources::GetResourcesOutput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_resources::GetResourcesOutput {
            output: self.output,
        })
    }
}
