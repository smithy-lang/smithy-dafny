// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetLongInput {
    #[allow(missing_docs)] // documentation missing in model
pub value: ::std::option::Option<::std::primitive::i64>,
}
impl GetLongInput {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(&self) -> ::std::option::Option<::std::primitive::i64> {
    self.value
}
}
impl GetLongInput {
    /// Creates a new builder-style object to manufacture [`GetLongInput`](crate::operation::operation::GetLongInput).
    pub fn builder() -> crate::operation::get_long_known_value_test::builders::GetLongInputBuilder {
        crate::operation::get_long_known_value_test::builders::GetLongInputBuilder::default()
    }
}

/// A builder for [`GetLongInput`](crate::operation::operation::GetLongInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetLongInputBuilder {
    pub(crate) value: ::std::option::Option<::std::primitive::i64>,
}
impl GetLongInputBuilder {
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
    /// Consumes the builder and constructs a [`GetLongInput`](crate::operation::operation::GetLongInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_long_known_value_test::GetLongInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_long_known_value_test::GetLongInput {
            value: self.value,
        })
    }
}
