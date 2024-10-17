// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
/// A service that supports the operation of getting things.
///
/// This is still part of the same documentation trait
/// even though it's separated.
///
/// It's also important to make sure we don't incorrectly
/// reject multiline plaintext comments
/// because we incorrectly think newlines are CommonMark
/// syntax.
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
    /// Creates a new builder-style object to manufacture [`GetThingInput`](crate::operation::get_thing::builders::GetThingInput).
    pub fn builder() -> crate::operation::get_thing::builders::GetThingInputBuilder {
        crate::operation::get_thing::builders::GetThingInputBuilder::default()
    }
}

/// A builder for [`GetThingInput`](crate::operation::operation::GetThingInput).
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
    /// Consumes the builder and constructs a [`GetThingInput`](crate::operation::operation::GetThingInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_thing::GetThingInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_thing::GetThingInput {
            name: self.name,
        })
    }
}
