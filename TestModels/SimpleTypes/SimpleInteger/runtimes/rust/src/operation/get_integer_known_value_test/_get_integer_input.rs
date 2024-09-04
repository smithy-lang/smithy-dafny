// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetIntegerInput {
    #[allow(missing_docs)] // documentation missing in model
pub value: ::std::option::Option<::std::primitive::i32>,
}
impl GetIntegerInput {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.value
}
}
impl GetIntegerInput {
    /// Creates a new builder-style object to manufacture [`GetIntegerInput`](crate::operation::operation::GetIntegerInput).
    pub fn builder() -> crate::operation::get_integer_known_value_test::builders::GetIntegerInputBuilder {
        crate::operation::get_integer_known_value_test::builders::GetIntegerInputBuilder::default()
    }
}

/// A builder for [`GetIntegerInput`](crate::operation::operation::GetIntegerInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetIntegerInputBuilder {
    pub(crate) value: ::std::option::Option<::std::primitive::i32>,
}
impl GetIntegerInputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(mut self, input: impl ::std::convert::Into<::std::primitive::i32>) -> Self {
    self.value = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_value(mut self, input: ::std::option::Option<::std::primitive::i32>) -> Self {
    self.value = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_value(&self) -> &::std::option::Option<::std::primitive::i32> {
    &self.value
}
    /// Consumes the builder and constructs a [`GetIntegerInput`](crate::operation::operation::GetIntegerInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_integer_known_value_test::GetIntegerInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_integer_known_value_test::GetIntegerInput {
            value: self.value,
        })
    }
}
