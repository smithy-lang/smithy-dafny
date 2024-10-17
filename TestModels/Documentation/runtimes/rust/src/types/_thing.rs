// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
/// A thing that you can get from the service.
pub struct Thing {
    /// The name of the thing.
pub name: ::std::option::Option<::std::string::String>,
}
impl Thing {
    /// The name of the thing.
pub fn name(&self) -> &::std::option::Option<::std::string::String> {
    &self.name
}
}
impl Thing {
    /// Creates a new builder-style object to manufacture [`Thing`](crate::types::Thing).
    pub fn builder() -> crate::types::builders::ThingBuilder {
        crate::types::builders::ThingBuilder::default()
    }
}

/// A builder for [`Thing`](crate::types::Thing).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct ThingBuilder {
    pub(crate) name: ::std::option::Option<::std::string::String>,
}
impl ThingBuilder {
    /// The name of the thing.
pub fn name(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.name = ::std::option::Option::Some(input.into());
    self
}
/// The name of the thing.
pub fn set_name(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.name = input;
    self
}
/// The name of the thing.
pub fn get_name(&self) -> &::std::option::Option<::std::string::String> {
    &self.name
}
    /// Consumes the builder and constructs a [`Thing`](crate::types::Thing).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::types::Thing,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::types::Thing {
            name: self.name,
        })
    }
}
