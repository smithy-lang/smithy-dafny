// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetStringUTF8Output {
    #[allow(missing_docs)] // documentation missing in model
pub value: ::std::option::Option<::std::string::String>,
}
impl GetStringUTF8Output {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(&self) -> ::std::option::Option<::std::string::String> {
    self.value.clone()
}
}
impl GetStringUTF8Output {
    /// Creates a new builder-style object to manufacture [`GetStringUTF8Output`](crate::operation::operation::GetStringUTF8Output).
    pub fn builder() -> crate::operation::get_string_utf8::builders::GetStringUTF8OutputBuilder {
        crate::operation::get_string_utf8::builders::GetStringUTF8OutputBuilder::default()
    }
}

/// A builder for [`GetStringUTF8Output`](crate::operation::operation::GetStringUTF8Output).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetStringUTF8OutputBuilder {
    pub(crate) value: ::std::option::Option<::std::string::String>,
}
impl GetStringUTF8OutputBuilder {
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
    /// Consumes the builder and constructs a [`GetStringUTF8Output`](crate::operation::operation::GetStringUTF8Output).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_string_utf8::GetStringUTF8Output,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_string_utf8::GetStringUTF8Output {
            value: self.value,
        })
    }
}
