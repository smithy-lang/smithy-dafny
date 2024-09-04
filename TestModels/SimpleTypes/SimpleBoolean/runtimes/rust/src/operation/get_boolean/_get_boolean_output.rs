// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetBooleanOutput {
    #[allow(missing_docs)] // documentation missing in model
pub value: ::std::option::Option<::std::primitive::bool>,
}
impl GetBooleanOutput {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(&self) -> &::std::option::Option<::std::primitive::bool> {
    &self.value
}
}
impl GetBooleanOutput {
    /// Creates a new builder-style object to manufacture [`GetBooleanOutput`](crate::operation::operation::GetBooleanOutput).
    pub fn builder() -> crate::operation::get_boolean::builders::GetBooleanOutputBuilder {
        crate::operation::get_boolean::builders::GetBooleanOutputBuilder::default()
    }
}

/// A builder for [`GetBooleanOutput`](crate::operation::operation::GetBooleanOutput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetBooleanOutputBuilder {
    pub(crate) value: ::std::option::Option<::std::primitive::bool>,
}
impl GetBooleanOutputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(mut self, input: impl ::std::convert::Into<::std::primitive::bool>) -> Self {
    self.value = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_value(mut self, input: ::std::option::Option<::std::primitive::bool>) -> Self {
    self.value = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_value(&self) -> &::std::option::Option<::std::primitive::bool> {
    &self.value
}
    /// Consumes the builder and constructs a [`GetBooleanOutput`](crate::operation::operation::GetBooleanOutput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_boolean::GetBooleanOutput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_boolean::GetBooleanOutput {
            value: self.value,
        })
    }
}
