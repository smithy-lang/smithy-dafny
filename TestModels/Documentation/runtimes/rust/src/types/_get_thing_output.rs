// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
/// Outputs for getting a thing.
pub struct GetThingOutput {
    /// The thing that you just got.
pub thing: ::std::option::Option<crate::types::Thing>,
}
impl GetThingOutput {
    /// The thing that you just got.
pub fn thing(&self) -> &::std::option::Option<crate::types::Thing> {
    &self.thing
}
}
impl GetThingOutput {
    /// Creates a new builder-style object to manufacture [`GetThingOutput`](crate::types::GetThingOutput).
    pub fn builder() -> crate::types::builders::GetThingOutputBuilder {
        crate::types::builders::GetThingOutputBuilder::default()
    }
}

/// A builder for [`GetThingOutput`](crate::types::GetThingOutput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetThingOutputBuilder {
    pub(crate) thing: ::std::option::Option<crate::types::Thing>,
}
impl GetThingOutputBuilder {
    /// The thing that you just got.
pub fn thing(mut self, input: impl ::std::convert::Into<crate::types::Thing>) -> Self {
    self.thing = ::std::option::Option::Some(input.into());
    self
}
/// The thing that you just got.
pub fn set_thing(mut self, input: ::std::option::Option<crate::types::Thing>) -> Self {
    self.thing = input;
    self
}
/// The thing that you just got.
pub fn get_thing(&self) -> &::std::option::Option<crate::types::Thing> {
    &self.thing
}
    /// Consumes the builder and constructs a [`GetThingOutput`](crate::types::GetThingOutput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::types::GetThingOutput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::types::GetThingOutput {
            thing: self.thing,
        })
    }
}
