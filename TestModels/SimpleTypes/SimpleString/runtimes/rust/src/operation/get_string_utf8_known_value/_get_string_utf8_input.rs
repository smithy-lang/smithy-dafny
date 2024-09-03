// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetStringUTF8Input {
    #[allow(missing_docs)] // documentation missing in model
pub value: ::std::option::Option<::std::string::String>,
}
impl GetStringUTF8Input {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(&self) -> ::std::option::Option<::std::string::String> {
    self.value.clone()
}
}
impl GetStringUTF8Input {
    /// Creates a new builder-style object to manufacture [`GetStringUTF8Input`](crate::operation::operation::GetStringUTF8Input).
    pub fn builder() -> crate::operation::get_string_utf8_known_value::builders::GetStringUTF8InputBuilder {
        crate::operation::get_string_utf8_known_value::builders::GetStringUTF8InputBuilder::default()
    }
}

/// A builder for [`GetStringUTF8Input`](crate::operation::operation::GetStringUTF8Input).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetStringUTF8InputBuilder {
    pub(crate) value: ::std::option::Option<::std::string::String>,
}
impl GetStringUTF8InputBuilder {
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
    /// Consumes the builder and constructs a [`GetStringUTF8Input`](crate::operation::operation::GetStringUTF8Input).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_string_utf8_known_value::GetStringUTF8Input,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_string_utf8_known_value::GetStringUTF8Input {
            value: self.value,
        })
    }
}
