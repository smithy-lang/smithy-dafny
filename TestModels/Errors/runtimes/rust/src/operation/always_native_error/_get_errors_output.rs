// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetErrorsOutput {
    #[allow(missing_docs)] // documentation missing in model
pub value: ::std::option::Option<::std::string::String>,
}
impl GetErrorsOutput {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(&self) -> &::std::option::Option<::std::string::String> {
    &self.value
}
}
impl GetErrorsOutput {
    /// Creates a new builder-style object to manufacture [`GetErrorsOutput`](crate::operation::always_native_error::builders::GetErrorsOutput).
    pub fn builder() -> crate::operation::always_native_error::builders::GetErrorsOutputBuilder {
        crate::operation::always_native_error::builders::GetErrorsOutputBuilder::default()
    }
}

/// A builder for [`GetErrorsOutput`](crate::operation::operation::GetErrorsOutput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetErrorsOutputBuilder {
    pub(crate) value: ::std::option::Option<::std::string::String>,
}
impl GetErrorsOutputBuilder {
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
    /// Consumes the builder and constructs a [`GetErrorsOutput`](crate::operation::operation::GetErrorsOutput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::always_native_error::GetErrorsOutput,
        crate::types::error::Error,
    > {
        ::std::result::Result::Ok(crate::operation::always_native_error::GetErrorsOutput {
            value: self.value,
        })
    }
}
