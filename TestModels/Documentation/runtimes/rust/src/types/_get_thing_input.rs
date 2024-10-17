// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
/// Inputs for getting a thing.
pub struct GetThingInput {
    /// The name of the thing to get, obviously.
pub name: ::std::option::Option<::std::string::String>,
}
impl GetThingInput {
    /// The name of the thing to get, obviously.
pub fn name(&self) -> &::std::option::Option<::std::string::String> {
    &self.name
}
}
impl GetThingInput {
    /// Creates a new builder-style object to manufacture [`GetThingInput`](crate::types::GetThingInput).
    pub fn builder() -> crate::types::builders::GetThingInputBuilder {
        crate::types::builders::GetThingInputBuilder::default()
    }
}

/// A builder for [`GetThingInput`](crate::types::GetThingInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetThingInputBuilder {
    pub(crate) name: ::std::option::Option<::std::string::String>,
}
impl GetThingInputBuilder {
    /// The name of the thing to get, obviously.
pub fn name(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.name = ::std::option::Option::Some(input.into());
    self
}
/// The name of the thing to get, obviously.
pub fn set_name(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.name = input;
    self
}
/// The name of the thing to get, obviously.
pub fn get_name(&self) -> &::std::option::Option<::std::string::String> {
    &self.name
}
    /// Consumes the builder and constructs a [`GetThingInput`](crate::types::GetThingInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::types::GetThingInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::types::GetThingInput {
            name: self.name,
        })
    }
}
