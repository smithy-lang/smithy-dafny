// Copyright Amazon.com Inc. or its affiliates. All Rights Reserved.
// SPDX-License-Identifier: Apache-2.0
// Do not modify this file. This file is machine generated, and any changes to it will be overwritten.
#[allow(missing_docs)] // documentation missing in model
#[non_exhaustive]
#[derive(::std::clone::Clone, ::std::cmp::PartialEq, ::std::fmt::Debug)]
pub struct GetEnumV2Input {
    #[allow(missing_docs)] // documentation missing in model
pub value: ::std::option::Option<crate::types::SimpleEnumV2Shape>,
}
impl GetEnumV2Input {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(&self) -> &::std::option::Option<crate::types::SimpleEnumV2Shape> {
    &self.value
}
}
impl GetEnumV2Input {
    /// Creates a new builder-style object to manufacture [`GetEnumV2Input`](crate::operation::operation::GetEnumV2Input).
    pub fn builder() -> crate::operation::get_enum_v2::builders::GetEnumV2InputBuilder {
        crate::operation::get_enum_v2::builders::GetEnumV2InputBuilder::default()
    }
}

/// A builder for [`GetEnumV2Input`](crate::operation::operation::GetEnumV2Input).
#[non_exhaustive]
#[derive(
    ::std::clone::Clone, ::std::cmp::PartialEq, ::std::default::Default, ::std::fmt::Debug,
)]
pub struct GetEnumV2InputBuilder {
    pub(crate) value: ::std::option::Option<crate::types::SimpleEnumV2Shape>,
}
impl GetEnumV2InputBuilder {
    #[allow(missing_docs)] // documentation missing in model
pub fn value(mut self, input: impl ::std::convert::Into<crate::types::SimpleEnumV2Shape>) -> Self {
    self.value = ::std::option::Option::Some(input.into());
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn set_value(mut self, input: ::std::option::Option<crate::types::SimpleEnumV2Shape>) -> Self {
    self.value = input;
    self
}
#[allow(missing_docs)] // documentation missing in model
pub fn get_value(&self) -> &::std::option::Option<crate::types::SimpleEnumV2Shape> {
    &self.value
}
    /// Consumes the builder and constructs a [`GetEnumV2Input`](crate::operation::operation::GetEnumV2Input).
    pub fn build(
        self,
    ) -> ::std::result::Result<
        crate::operation::get_enum_v2::GetEnumV2Input,
        ::aws_smithy_types::error::operation::BuildError,
    > {
        ::std::result::Result::Ok(crate::operation::get_enum_v2::GetEnumV2Input {
            value: self.value,
        })
    }
}
