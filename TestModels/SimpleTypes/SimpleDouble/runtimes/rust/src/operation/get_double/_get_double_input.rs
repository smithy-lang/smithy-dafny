// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetDoubleInput {
    #[allow(missing_docs)] // documentation missing in model
pub value: ::std::option::Option<::std::primitive::f64>,
}
impl GetDoubleInput {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(&self) -> ::std::option::Option<::std::primitive::f64> {
    self.value
}
}
impl GetDoubleInput {
    /// Creates a new builder-style object to manufacture [`GetDoubleInput`](crate::operation::operation::GetDoubleInput).
    pub fn builder() -> crate::operation::get_double::builders::GetDoubleInputBuilder {
        crate::operation::get_double::builders::GetDoubleInputBuilder::default()
    }
}

/// A builder for [`GetDoubleInput`](crate::operation::operation::GetDoubleInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetDoubleInputBuilder {
    pub(crate) value: ::std::option::Option<::std::primitive::f64>,
}
impl GetDoubleInputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(mut self, input: impl ::std::convert::Into<::std::primitive::f64>) -> Self {
    self.value = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_value(mut self, input: ::std::option::Option<::std::primitive::f64>) -> Self {
    self.value = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_value(&self) -> &::std::option::Option<::std::primitive::f64> {
    &self.value
}
    /// Consumes the builder and constructs a [`GetDoubleInput`](crate::operation::operation::GetDoubleInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_double::GetDoubleInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_double::GetDoubleInput {
            value: self.value,
        })
    }
}
