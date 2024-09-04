// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetStringUtf8Output {
    #[allow(missing_docs)] // documentation missing in model
pub value: ::std::option::Option<::std::string::String>,
}
impl GetStringUtf8Output {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(&self) -> &::std::option::Option<::std::string::String> {
    &self.value
}
}
impl GetStringUtf8Output {
    /// Creates a new builder-style object to manufacture [`GetStringUtf8Output`](crate::operation::operation::GetStringUtf8Output).
    pub fn builder() -> crate::operation::get_string_utf8_known_value::builders::GetStringUtf8OutputBuilder {
        crate::operation::get_string_utf8_known_value::builders::GetStringUtf8OutputBuilder::default()
    }
}

/// A builder for [`GetStringUtf8Output`](crate::operation::operation::GetStringUtf8Output).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetStringUtf8OutputBuilder {
    pub(crate) value: ::std::option::Option<::std::string::String>,
}
impl GetStringUtf8OutputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(mut self, input: impl ::std::convert::Into<::std::string::String>) -> Self {
    self.value = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_value(mut self, input: ::std::option::Option<::std::string::String>) -> Self {
    self.value = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_value(&self) -> &::std::option::Option<::std::string::String> {
    &self.value
}
    /// Consumes the builder and constructs a [`GetStringUtf8Output`](crate::operation::operation::GetStringUtf8Output).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_string_utf8_known_value::GetStringUtf8Output,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_string_utf8_known_value::GetStringUtf8Output {
            value: self.value,
        })
    }
}
