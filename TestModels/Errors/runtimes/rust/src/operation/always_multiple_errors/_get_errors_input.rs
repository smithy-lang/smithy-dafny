// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetErrorsInput {
    #[allow(missing_docs)] // documentation missing in model
pub value: ::std::option::Option<::std::string::String>,
}
impl GetErrorsInput {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(&self) -> &::std::option::Option<::std::string::String> {
    &self.value
}
}
impl GetErrorsInput {
    /// Creates a new builder-style object to manufacture [`GetErrorsInput`](crate::operation::always_multiple_errors::builders::GetErrorsInput).
    pub fn builder() -> crate::operation::always_multiple_errors::builders::GetErrorsInputBuilder {
        crate::operation::always_multiple_errors::builders::GetErrorsInputBuilder::default()
    }
}

/// A builder for [`GetErrorsInput`](crate::operation::operation::GetErrorsInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetErrorsInputBuilder {
    pub(crate) value: ::std::option::Option<::std::string::String>,
}
impl GetErrorsInputBuilder {
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
    /// Consumes the builder and constructs a [`GetErrorsInput`](crate::operation::operation::GetErrorsInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::always_multiple_errors::GetErrorsInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::always_multiple_errors::GetErrorsInput {
            value: self.value,
        })
    }
}
