// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetTimestampInput {
    #[allow(missing_docs)] // documentation missing in model
pub value: ::std::option::Option<::aws_smithy_types::DateTime>,
}
impl GetTimestampInput {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(&self) -> &::std::option::Option<::aws_smithy_types::DateTime> {
    &self.value
}
}
impl GetTimestampInput {
    /// Creates a new builder-style object to manufacture [`GetTimestampInput`](crate::operation::operation::GetTimestampInput).
    pub fn builder() -> crate::operation::get_timestamp::builders::GetTimestampInputBuilder {
        crate::operation::get_timestamp::builders::GetTimestampInputBuilder::default()
    }
}

/// A builder for [`GetTimestampInput`](crate::operation::operation::GetTimestampInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetTimestampInputBuilder {
    pub(crate) value: ::std::option::Option<::aws_smithy_types::DateTime>,
}
impl GetTimestampInputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(mut self, input: impl ::std::convert::Into<::aws_smithy_types::DateTime>) -> Self {
    self.value = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_value(mut self, input: ::std::option::Option<::aws_smithy_types::DateTime>) -> Self {
    self.value = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_value(&self) -> &::std::option::Option<::aws_smithy_types::DateTime> {
    &self.value
}
    /// Consumes the builder and constructs a [`GetTimestampInput`](crate::operation::operation::GetTimestampInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_timestamp::GetTimestampInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_timestamp::GetTimestampInput {
            value: self.value,
        })
    }
}
