// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetTimestampOutput {
    #[allow(missing_docs)] // documentation missing in model
pub value: ::std::option::Option<::aws_smithy_types::DateTime>,
}
impl GetTimestampOutput {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(&self) -> &::std::option::Option<::aws_smithy_types::DateTime> {
    &self.value
}
}
impl GetTimestampOutput {
    /// Creates a new builder-style object to manufacture [`GetTimestampOutput`](crate::operation::operation::GetTimestampOutput).
    pub fn builder() -> crate::operation::get_timestamp::builders::GetTimestampOutputBuilder {
        crate::operation::get_timestamp::builders::GetTimestampOutputBuilder::default()
    }
}

/// A builder for [`GetTimestampOutput`](crate::operation::operation::GetTimestampOutput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetTimestampOutputBuilder {
    pub(crate) value: ::std::option::Option<::aws_smithy_types::DateTime>,
}
impl GetTimestampOutputBuilder {
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
    /// Consumes the builder and constructs a [`GetTimestampOutput`](crate::operation::operation::GetTimestampOutput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_timestamp::GetTimestampOutput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_timestamp::GetTimestampOutput {
            value: self.value,
        })
    }
}
