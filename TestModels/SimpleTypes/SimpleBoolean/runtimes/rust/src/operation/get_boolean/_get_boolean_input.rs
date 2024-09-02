// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetBooleanInput {
    #[allow(missing_docs)] // documentation missing in model
pub value: ::std::option::Option<::std::primitive::bool>,
}
impl GetBooleanInput {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(&self) -> ::std::option::Option<::std::primitive::bool> {
    self.value
}
}
impl GetBooleanInput {
    /// Creates a new builder-style object to manufacture [`GetBooleanInput`](crate::operation::operation::GetBooleanInput).
    pub fn builder() -> crate::operation::get_boolean::builders::GetBooleanInputBuilder {
        crate::operation::get_boolean::builders::GetBooleanInputBuilder::default()
    }
}

/// A builder for [`GetBooleanInput`](crate::operation::operation::GetBooleanInput).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetBooleanInputBuilder {
    pub(crate) value: ::std::option::Option<::std::primitive::bool>,
}
impl GetBooleanInputBuilder {
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
    /// Consumes the builder and constructs a [`GetBooleanInput`](crate::operation::operation::GetBooleanInput).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_boolean::GetBooleanInput,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_boolean::GetBooleanInput {
            value: self.value,
        })
    }
}
