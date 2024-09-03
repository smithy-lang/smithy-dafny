// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetLongOutput {
    #[allow(missing_docs)] // documentation missing in model
pub value: ::std::option::Option<::std::primitive::i64>,
}
impl GetLongOutput {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(&self) -> ::std::option::Option<::std::primitive::i64> {
    self.value
}
}
impl GetLongOutput {
    /// Creates a new builder-style object to manufacture [`GetLongOutput`](crate::operation::operation::GetLongOutput).
    pub fn builder() -> crate::operation::get_long::builders::GetLongOutputBuilder {
        crate::operation::get_long::builders::GetLongOutputBuilder::default()
    }
}

/// A builder for [`GetLongOutput`](crate::operation::operation::GetLongOutput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetLongOutputBuilder {
    pub(crate) value: ::std::option::Option<::std::primitive::i64>,
}
impl GetLongOutputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(mut self, input: impl ::std::convert::Into<::std::primitive::i64>) -> Self {
    self.value = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_value(mut self, input: ::std::option::Option<::std::primitive::i64>) -> Self {
    self.value = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_value(&self) -> &::std::option::Option<::std::primitive::i64> {
    &self.value
}
    /// Consumes the builder and constructs a [`GetLongOutput`](crate::operation::operation::GetLongOutput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_long::GetLongOutput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_long::GetLongOutput {
            value: self.value,
        })
    }
}
