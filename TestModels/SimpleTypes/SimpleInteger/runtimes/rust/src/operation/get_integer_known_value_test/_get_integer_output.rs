// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetIntegerOutput {
    #[allow(missing_docs)] // documentation missing in model
pub value: ::std::option::Option<::std::primitive::i32>,
}
impl GetIntegerOutput {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(&self) -> ::std::option::Option<::std::primitive::i32> {
    self.value
}
}
impl GetIntegerOutput {
    /// Creates a new builder-style object to manufacture [`GetIntegerOutput`](crate::operation::operation::GetIntegerOutput).
    pub fn builder() -> crate::operation::get_integer_known_value_test::builders::GetIntegerOutputBuilder {
        crate::operation::get_integer_known_value_test::builders::GetIntegerOutputBuilder::default()
    }
}

/// A builder for [`GetIntegerOutput`](crate::operation::operation::GetIntegerOutput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetIntegerOutputBuilder {
    pub(crate) value: ::std::option::Option<::std::primitive::i32>,
}
impl GetIntegerOutputBuilder {
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
    /// Consumes the builder and constructs a [`GetIntegerOutput`](crate::operation::operation::GetIntegerOutput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_integer_known_value_test::GetIntegerOutput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_integer_known_value_test::GetIntegerOutput {
            value: self.value,
        })
    }
}
